//! The `ffi` macro allows you to easily export FFI interfaces for your Rust code with minimal
//! boilerplate. It is designed to facilitate several unique use cases which commonly occur in
//! FFI code, particularly where a Rust shared library is `dlopen`ed by a C program and called
//! into.
//!
//! * Callbacks from C to Rust code using opaque pointers to Rust objects
//! * Callbacks in C code to Rust code where passing a closure is preferred to passing a
//!   function pointer, for example where state capture is desired.

#![deny(clippy::unwrap_used)]
#![forbid(unsafe_code)]

use darling::{
    ast::NestedMeta,
    util::{Flag, WithOriginal},
    Error, FromAttributes, FromMeta, Result,
};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use proc_macro_error::{abort, proc_macro_error};
use quote::{format_ident, quote};
use std::collections::HashMap;
use syn::{
    parse_macro_input, parse_str, FnArg, GenericArgument, ImplGenerics, ImplItem, ImplItemFn,
    ItemImpl, Pat, PathArguments, ReturnType, Type, TypeGenerics, WhereClause,
};

#[derive(Debug, Clone, FromMeta)]
#[darling(and_then = "Self::validate")]
/// Options for an argument to an ffi method
struct FfiMethodOptArg {
    #[darling(rename = "self")]
    /// Whether this argument needs to be converted to the receiver type
    receiver: Flag,
    #[darling(default)]
    ty: Option<String>,
    #[darling(default)]
    rename: Option<String>,
    rest: Flag,
}

impl FfiMethodOptArg {
    fn validate(self) -> Result<Self> {
        if self.receiver.is_present() && self.rest.is_present() {
            Err(Error::custom(
                "An argument may either be self or have rest enabled.",
            ))
        } else if self.rest.is_present() && (self.ty.is_some() || self.rename.is_some()) {
            Err(Error::custom(
                "The rest argument may not specify a rename or type change",
            ))
        } else {
            Ok(self)
        }
    }
}

#[derive(Debug, FromAttributes)]
#[darling(
    attributes(ffi),
    forward_attrs(
        cfg,
        derive,
        allow,
        warn,
        deny,
        forbid,
        deprecated,
        must_use,
        doc,
        non_exhaustive
    )
)]
struct FfiMethodOpts {
    expect: Flag,
    #[darling(default)]
    visibility: Option<String>,
    #[darling(default)]
    name: Option<String>,
    #[darling(multiple)]
    arg: Vec<FfiMethodOptArg>,
}

impl FfiMethodOpts {
    fn visibility(&self) -> TokenStream2 {
        if let Some(ref visibility) = self.visibility {
            match parse_str(visibility) {
                Ok(visibility) => visibility,
                Err(e) => Error::from(e).write_errors(),
            }
        } else {
            // NOTE: Default is "pub" because typically this is required for FFI
            quote!(pub)
        }
    }
}

#[derive(Debug)]
struct FfiMethods<'a> {
    ffi_self_ty: Option<Type>,
    expect: Flag,
    self_ty: Type,
    self_generics: (ImplGenerics<'a>, TypeGenerics<'a>, Option<&'a WhereClause>),
    ffi_methods: Vec<WithOriginal<FfiMethodOpts, ImplItemFn>>,
    other_items: Vec<&'a ImplItem>,
}

impl<'a> FfiMethods<'a> {
    fn try_from(value: &'a ItemImpl, ffi_self_ty: Option<Type>, expect: Flag) -> Result<Self> {
        let self_generics = value.generics.split_for_impl();
        let mut ffi_methods = Vec::new();
        let mut other_items = Vec::new();
        let mut errors = Vec::new();

        value.items.iter().for_each(|i| {
            if let ImplItem::Fn(ref f) = i {
                match FfiMethodOpts::from_attributes(&f.attrs) {
                    Ok(opts) => {
                        let mut f = f.clone();
                        // NOTE: This effectively makes splitting the ffi() macro across multiple invocations
                        // an error. I'm okay with that, I don't like the syntax and it'll break the argument
                        // ordering anyway.
                        f.attrs
                            .retain(|a| FfiMethodOpts::from_attributes(&[a.clone()]).is_err());
                        ffi_methods.push(WithOriginal::new(opts, f));
                    }
                    Err(e) => errors.push(e),
                }
            } else {
                other_items.push(i);
            }
        });

        if !errors.is_empty() {
            Err(Error::multiple(errors))
        } else {
            Ok(Self {
                ffi_self_ty,
                expect,
                self_ty: *value.self_ty.clone(),
                self_generics,
                ffi_methods,
                other_items,
            })
        }
    }
}

impl<'a> FfiMethods<'a> {
    fn original(&self) -> TokenStream2 {
        let orig_ffi_methods = self
            .ffi_methods
            .iter()
            .map(|m| &m.original)
            .collect::<Vec<_>>();

        let other_items = &self.other_items;

        quote! {
            #(#orig_ffi_methods)*
            #(#other_items)*
        }
    }

    fn ffi_return_ty(return_ty: &ReturnType, expect: bool) -> (TokenStream2, TokenStream2, bool) {
        if expect {
            if let ReturnType::Type(_, t) = return_ty {
                if let Type::Path(p) = &**t {
                    if let Some(last) = p.path.segments.last() {
                        if last.ident == "Result" {
                            if let PathArguments::AngleBracketed(a) = &last.arguments {
                                return (
                                    quote!(#return_ty),
                                    a.args
                                        .first()
                                        .map(|a| quote!(-> #a))
                                        .unwrap_or(quote!(#return_ty)),
                                    true,
                                );
                            }
                        }
                    }
                }
            }
        }

        (quote!(#return_ty), quote!(#return_ty), false)
    }

    fn ffi_func_name(&self, method: &WithOriginal<FfiMethodOpts, ImplItemFn>) -> TokenStream2 {
        method
            .parsed
            .name
            .as_ref()
            .map(|n| {
                let name = format_ident!("{n}");
                quote!(#name)
            })
            .unwrap_or({
                let name = &method.original.sig.ident;
                quote!(#name)
            })
    }

    fn ffi_func_args(
        &self,
        method: &WithOriginal<FfiMethodOpts, ImplItemFn>,
    ) -> Result<(
        Option<TokenStream2>,
        Vec<TokenStream2>,
        HashMap<usize, (String, Box<Type>)>,
    )> {
        let impl_method_args = method.original.sig.inputs.iter().collect::<Vec<_>>();
        let impl_method_args_no_receiver = method
            .original
            .sig
            .inputs
            .iter()
            .filter(|a| !matches!(a, FnArg::Receiver(_)))
            .cloned()
            .collect::<Vec<_>>();
        let mut ffi_receiver_name = None;
        let mut ffi_func_args = Vec::new();
        let mut ffi_func_renames = HashMap::new();

        for (i, arg) in method.parsed.arg.iter().enumerate() {
            if arg.receiver.is_present() {
                let ty = if let Some(ref ty) = arg.ty {
                    match parse_str::<Type>(ty) {
                        Ok(ty) => quote!(#ty),
                        Err(e) => Error::from(e).write_errors(),
                    }
                } else if let Some(ref ty) = self.ffi_self_ty {
                    quote!(#ty)
                } else {
                    let ty = &self.self_ty;
                    quote!(#ty)
                };

                let name = arg
                    .rename
                    .as_ref()
                    .map(|n| {
                        let n = format_ident!("{n}");
                        quote!(#n)
                    })
                    .unwrap_or(quote!(slf));
                ffi_func_args.push(quote!(#name: #ty));
                ffi_receiver_name = Some(name);
            } else if arg.rest.is_present() {
                // If we have already seen the receiver argument, we need to look one
                // argument forward
                let mut arg_index = i;

                if ffi_receiver_name.is_none() {
                    arg_index += 1;
                }

                ffi_func_args.extend(
                    impl_method_args_no_receiver
                        .iter()
                        .enumerate()
                        .filter_map(|(i, a)| (i >= arg_index - 1).then_some(a))
                        .map(|a| quote!(#a)),
                );
            } else if ffi_func_args.len() <= impl_method_args_no_receiver.len() + 1 {
                // If we have already seen the receiver argument, we need to look one
                // argument forward
                let mut arg_index = i;

                if ffi_receiver_name.is_none() {
                    arg_index += 1;
                }

                let Some(FnArg::Typed(impl_method_arg_pat_type)) = impl_method_args.get(arg_index)
                else {
                    return Err(Error::custom(
                        "Argument is not a typed argument while getting ffi function arguments",
                    ));
                };

                let ty = &impl_method_arg_pat_type.ty;
                if let Some(ref rename) = arg.rename {
                    ffi_func_renames.insert(i, (rename.clone(), ty.clone()));
                    ffi_func_args.push({
                        let rename = format_ident!("{rename}");
                        quote!(#rename: #ty)
                    });
                } else {
                    ffi_func_args.push(quote!(#impl_method_arg_pat_type));
                }
            } else {
                return Err(Error::custom(
                    "Argument is not a typed argument while getting ffi function arguments",
                ));
            }
        }

        Ok((ffi_receiver_name, ffi_func_args, ffi_func_renames))
    }

    fn ffi_method_call(
        &self,
        method: &WithOriginal<FfiMethodOpts, ImplItemFn>,
        ffi_receiver_name: &Option<TokenStream2>,
        ffi_func_renames: &HashMap<usize, (String, Box<Type>)>,
        need_expect: bool,
    ) -> TokenStream2 {
        let impl_method_args_no_receiver = method
            .original
            .sig
            .inputs
            .iter()
            .filter(|a| !matches!(a, FnArg::Receiver(_)))
            .cloned()
            .collect::<Vec<_>>();
        let Some(impl_method_receiver) = method.original.sig.receiver() else {
            abort!(method.original, "No receiver on method");
        };

        let maybe_mut_ref = impl_method_receiver.mutability.map(|m| quote!(#m));
        let self_ty = &self.self_ty;
        let Some(self_name) = ffi_receiver_name else {
            return Error::custom("No receiver name").write_errors();
        };
        let impl_method_name = &method.original.sig.ident;
        let mut impl_method_call_args = Vec::new();
        for (i, arg) in impl_method_args_no_receiver.iter().enumerate() {
            if let Some((rename, _ty)) = ffi_func_renames.get(&i) {
                let ident = format_ident!("{rename}");
                impl_method_call_args.push(quote!(#ident));
            } else {
                let FnArg::Typed(ref typed) = arg else {
                    return Error::custom(format!("Argument {i} is not a typed argument"))
                        .write_errors();
                };
                let Pat::Ident(ref ident) = &*typed.pat else {
                    return Error::custom("Pattern is not an identifier").write_errors();
                };
                let ident = &ident.ident;
                impl_method_call_args.push(quote!(#ident));
            }
        }
        let impl_maybe_expect = ((method.parsed.expect.is_present() || self.expect.is_present())
            && need_expect)
            .then_some({
                let expect_message =
                    format!("Failed to execute FFI method {}", method.original.sig.ident);
                quote!(.expect(#expect_message))
            })
            .unwrap_or_default();
        quote! {
            Into::<&#maybe_mut_ref #self_ty>::into(#self_name).#impl_method_name(
                #(#impl_method_call_args),*
            )#impl_maybe_expect
        }
    }

    fn ffi_method(&self, method: &WithOriginal<FfiMethodOpts, ImplItemFn>) -> Result<TokenStream2> {
        let ffi_func_name = self.ffi_func_name(method);
        let (ffi_receiver_name, ffi_func_args, ffi_func_renames) = self.ffi_func_args(method)?;

        let (_impl_method_return_ty, ffi_func_return_ty, need_expect) = Self::ffi_return_ty(
            &method.original.sig.output,
            method.parsed.expect.is_present() || self.expect.is_present(),
        );

        let impl_method_args_no_receiver = method
            .original
            .sig
            .inputs
            .iter()
            .filter(|a| !matches!(a, FnArg::Receiver(_)))
            .cloned()
            .collect::<Vec<_>>();

        let mut impl_method_call_args = Vec::new();

        for (i, arg) in impl_method_args_no_receiver.iter().enumerate() {
            if let Some((rename, _ty)) = ffi_func_renames.get(&i) {
                let ident = format_ident!("{rename}");
                impl_method_call_args.push(quote!(#ident));
            } else {
                let FnArg::Typed(ref typed) = arg else {
                    return Err(Error::custom(format!(
                        "Argument {i} is not a typed argument"
                    )));
                };
                let Pat::Ident(ref ident) = &*typed.pat else {
                    return Err(Error::custom("Pattern is not an identifier"));
                };
                let ident = &ident.ident;
                impl_method_call_args.push(quote!(#ident));
            }
        }

        let ffi_func_visibility = method.parsed.visibility();
        let (_self_impl_genrics, self_ty_generics, self_where_clause) = &self.self_generics;

        let impl_method_call =
            self.ffi_method_call(method, &ffi_receiver_name, &ffi_func_renames, need_expect);

        Ok(quote! {
            #[no_mangle]
            #ffi_func_visibility extern "C" fn #ffi_func_name #self_ty_generics(
                #(#ffi_func_args),*
            ) #ffi_func_return_ty #self_where_clause {
                #impl_method_call
            }
        })
    }

    fn ffi(&self) -> Result<TokenStream2> {
        let methods = self
            .ffi_methods
            .iter()
            .map(|m| self.ffi_method(m))
            .collect::<Result<Vec<_>>>()?;

        Ok(quote! {
            #(#methods)*
        })
    }
}

#[derive(Debug, FromMeta)]
/// Arguments to the `#[ffi()]` macro
struct FfiOpts {
    #[darling(default, rename = "mod_name")]
    /// The name of the module to create to contain the FFI functions. Defaults to the name of
    /// the type being implemented, converted to lowercase.
    name: Option<String>,
    #[darling(default)]
    /// The visibility of the module to create to contain the FFI functions. Defaults to `pub`.
    visibility: Option<String>,
    #[darling(default)]
    /// The self type to use for the receiver argument for all methods. Defaults to a mut
    /// pointer to the type being implemented.
    self_ty: Option<String>,
    /// Whether method which return a `Result` should be `.expect`-ed
    expect: Flag,
    /// Whether to generate `From<T>` where T is the type specified in `self_ty`.
    from_ptr: Flag,
    /// Whether to generate `From<*mut T>`
    from_any_ptr: Flag,
}

impl FfiOpts {
    /// Generate the FFI implementation for this `impl`
    fn generate(&self, input: &ItemImpl) -> Result<TokenStream> {
        let methods = match FfiMethods::try_from(
            input,
            self.self_ty
                .as_ref()
                .and_then(|s| parse_str::<Type>(s).ok()),
            self.expect,
        ) {
            Ok(o) => o,
            Err(e) => return Err(e),
        };

        let original_impl = self.original_impl(input, methods.original());
        let maybe_from_ptr_impl = self.maybe_from_ptr_impl(input);
        let maybe_from_any_ptr_impl = self.maybe_from_any_ptr_impl(input);
        let ffi_mod = self.ffi_mod(input, methods.ffi()?);

        Ok(quote! {
            #original_impl

            #maybe_from_ptr_impl

            #maybe_from_any_ptr_impl

            #ffi_mod

        }
        .into())
    }

    fn input_name(&self, input: &ItemImpl) -> TokenStream2 {
        let Type::Path(p) = &*input.self_ty else {
            abort!(input, "Self type must be path");
        };

        let Some(last) = p.path.segments.last() else {
            abort!(input, "Self type must have segments");
        };

        match last.arguments {
            PathArguments::None => {
                let name = &input.self_ty;
                quote!(#name)
            }
            PathArguments::AngleBracketed(_) => {
                let last_ident = &last.ident;
                let mut segments = p.path.segments.iter().cloned().collect::<Vec<_>>();
                segments.pop();
                let segments = segments.iter().map(|s| quote!(#s)).collect::<Vec<_>>();
                quote!(#(#segments)::*#last_ident)
            }
            PathArguments::Parenthesized(_) => {
                abort!(input, "Parenthesized path arguments are not allowed here")
            }
        }
    }

    fn self_type_generics(&self, input: &ItemImpl) -> Vec<GenericArgument> {
        let Type::Path(p) = &*input.self_ty else {
            abort!(input, "Self type must be path");
        };

        let Some(last) = p.path.segments.last() else {
            abort!(input, "Self type must have segments");
        };

        match last.arguments {
            PathArguments::None => {
                vec![]
            }
            PathArguments::AngleBracketed(ref a) => a.args.clone().into_iter().collect::<Vec<_>>(),
            PathArguments::Parenthesized(_) => {
                abort!(input, "Parenthesized path arguments are not allowed here")
            }
        }
    }

    fn original_impl(&self, input: &ItemImpl, original: TokenStream2) -> TokenStream2 {
        // Extract the trait component of the `impl X (for Y) {` item. We need this in addition to the
        // generics below because we re-emit the original implementation.
        let maybe_trait = input.trait_.as_ref().map(|(not, path, f)| {
            let maybe_not = not.map(|not| quote!(#not)).unwrap_or_default();
            quote!(#maybe_not #path #f)
        });

        let impl_generics = &input.generics.params.iter().collect::<Vec<_>>();
        let where_clause = &input.generics.where_clause;
        let input_name = self.input_name(input);
        let self_type_generics = self.self_type_generics(input);

        let maybe_impl_generics = if impl_generics.is_empty() {
            quote!()
        } else {
            quote!(<#(#impl_generics),*>)
        };

        let maybe_self_type_generics = if self_type_generics.is_empty() {
            quote!()
        } else {
            quote!(<#(#self_type_generics),*>)
        };

        quote! {
            impl #maybe_impl_generics #maybe_trait #input_name #maybe_self_type_generics #where_clause {
                #original
            }
        }
    }

    fn maybe_from_ptr_impl(&self, input: &ItemImpl) -> TokenStream2 {
        let input_name = self.input_name(input);
        let self_type_generics = self.self_type_generics(input);
        let impl_generics_from = self
            .self_type_generics(input)
            .iter()
            .map(|g| quote!(#g))
            .collect::<Vec<_>>();
        self.from_ptr.is_present()
            .then_some(
                self
                .self_ty
                .as_ref()
                .and_then(|st| {
                    parse_str(st).ok().map(|stp: Type| {
                        quote! {
                            impl<#(#impl_generics_from),*> From<#stp> for &'static mut #input_name<#(#self_type_generics),*> {
                                fn from(value: #stp) -> Self {
                                    let ptr: *mut #input_name <#(#self_type_generics),*>= value as *mut #input_name <#(#self_type_generics),*>;
                                    unsafe { &mut *ptr }
                                }
                            }

                            impl<#(#impl_generics_from),*> From<#stp> for &'static #input_name <#(#self_type_generics),*> {
                                fn from(value: #stp) -> Self {
                                    let ptr: *mut #input_name <#(#self_type_generics),*> = value as *mut #input_name <#(#self_type_generics),*>;
                                    unsafe { &*ptr }
                                }
                            }
                        }
                    })
                })
            )
            .flatten()
            .unwrap_or_default()
    }

    fn maybe_from_any_ptr_impl(&self, input: &ItemImpl) -> TokenStream2 {
        let input_name = self.input_name(input);
        let self_type_generics = self.self_type_generics(input);
        let impl_generics_from = self
            .self_type_generics(input)
            .iter()
            .map(|g| quote!(#g))
            .collect::<Vec<_>>();
        self.from_any_ptr.is_present().then_some(quote! {
            impl<#(#impl_generics_from),*> From<*mut T> for &'static mut #input_name<#(#self_type_generics),*> {
                fn from(value: *mut T) -> Self {
                    let ptr: *mut #input_name <#(#self_type_generics),*>= value as *mut #input_name <#(#self_type_generics),*>;
                    unsafe { &mut *ptr }
                }
            }

            impl<#(#impl_generics_from),*> From<*mut T> for &'static #input_name<#(#self_type_generics),*> {
                fn from(value: *mut T) -> Self {
                    let ptr: *mut #input_name <#(#self_type_generics),*> = value as *mut #input_name <#(#self_type_generics),*>;
                    unsafe { &*ptr }
                }
            }

            impl<#(#impl_generics_from),*> From<*const T> for &'static #input_name<#(#self_type_generics),*> {
                fn from(value: *const T) -> Self {
                    let ptr: *const #input_name <#(#self_type_generics),*> = value as *const #input_name <#(#self_type_generics),*>;
                    unsafe { &*ptr }
                }
            }
        }).unwrap_or_default()
    }

    fn ffi_mod(&self, input: &ItemImpl, ffi: TokenStream2) -> TokenStream2 {
        let visibility = if let Some(ref visibility) = self.visibility {
            match parse_str(visibility) {
                Ok(visibility) => visibility,
                Err(e) => Error::from(e).write_errors(),
            }
        } else {
            // NOTE: Defaults to public visibility, because this is typically requred for FFI
            quote!(pub)
        };

        let name = self.module_name(input);

        quote! {
            #visibility mod #name {
                use super::*;
                #ffi
            }
        }
    }

    fn module_name(&self, input: &ItemImpl) -> TokenStream2 {
        match self.name.as_ref().map(|n| {
            let n = format_ident!("{n}");
            quote!(#n)
        }) {
            Some(n) => n,
            None => {
                let Type::Path(path) = input.self_ty.as_ref() else {
                    abort!(input, "Implementation self type is not a path");
                };

                let Some(name) = path.path.segments.first() else {
                    abort!(path, "Path has no segments");
                };

                let ffi_mod_name = format_ident!("{}", name.ident.to_string().to_ascii_lowercase());

                quote!(#ffi_mod_name)
            }
        }
    }
}

#[proc_macro_attribute]
#[proc_macro_error]
///
pub fn ffi(args: TokenStream, input: TokenStream) -> TokenStream {
    let meta = match NestedMeta::parse_meta_list(args.into()) {
        Ok(o) => o,
        Err(e) => return TokenStream::from(Error::from(e).write_errors()),
    };

    let options = match FfiOpts::from_list(&meta) {
        Ok(o) => o,
        Err(e) => return TokenStream::from(e.write_errors()),
    };

    let impl_item = parse_macro_input!(input as ItemImpl);

    options
        .generate(&impl_item)
        .unwrap_or_else(|e| TokenStream::from(e.write_errors()))
}
