# FFI

This crate helps expose Rust code via FFI to other languages, particularly C, by
providing an attribute `#[ffi]` which automatically implements call forwarding from
C-compatible function pointers to Rust `impl` methods.

This is particularly helpful when writing a shared libary in Rust which may be
`dlopen`-ed by a C program like QEMU.

## Example

In this example, imagine `run_callback` is in a C library you don't own. However, you
want to use the common `userdata` parameter of callback-registering functions to call
through to your struct instance. `ffi` allows you to export your `impl`'s methods as
C FFI compatible functions so you can easily call back and forth between languages.

`ffi` makes no assumptions about the parameter ordering of the callback types the C
code calling your Rust code expects, so it makes it easy to customize the generation for
your needs. It also provides utilities for automatically deriving conversions from raw
pointers like `From<*mut T> for &mut Foo`.

```rust
use ffi::ffi;

extern "C" fn run_callback(
    callback: extern "C" fn(*mut std::ffi::c_void, i32, i32, i32) -> i32,
    data: *mut std::ffi::c_void,
) -> i32 {
    callback(data, 1, 2, 3)
}

extern "C" fn run_callback_reverse(
    callback: extern "C" fn(i32, i32, i32, *mut std::ffi::c_void) -> i32,
    data: *mut std::ffi::c_void,
) -> i32 {
    callback(1, 2, 3, data)
}


#[derive(Debug, Clone, PartialEq, Eq)]
struct Vec3 {
    x: i32,
    y: i32,
    z: i32,
}

#[ffi(from_ptr, self_ty = "*mut std::ffi::c_void")]
impl Vec3 {
    #[ffi(arg(self), arg(rest))]
    fn add(&mut self, x: i32, y: i32, z: i32) -> i32 {
        self.x += x;
        self.y += y;
        self.z += z;
        self.x + self.y + self.z
    }

    #[ffi(arg(rest), arg(self))]
    fn add_reverse_args(&mut self, x: i32, y: i32, z: i32) -> i32 {
        self.add(x, y, z)
    }
}

fn main() {
    let mut v = Vec3 { x: 1, y: 2, z: 3 };

    run_callback(vec3::add, &mut v as *mut Vec3 as *mut _);

    assert_eq!(v, Vec3 { x: 2, y: 4, z: 6 })

    run_callback_reverse(vec3::add_reverse_args, &mut v as *mut Vec3 as *mut _);

    assert_eq!(v, Vec3 { x: 3, y: 6, z: 9});
}
```