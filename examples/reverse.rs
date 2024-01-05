// Copyright (C) 2024 Rowan Hart
// SPDX-License-Identifier: Apache-2.0

use ffi::ffi;

extern "C" fn run_callback_reverse(
    callback: extern "C" fn(i32, i32, i32, *mut std::ffi::c_void),
    data: *mut std::ffi::c_void,
) {
    callback(1, 2, 3, data);
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Vec3 {
    x: i32,
    y: i32,
    z: i32,
}

#[ffi(from_ptr, self_ty = "*mut std::ffi::c_void")]
impl Vec3 {
    #[ffi(arg(rest), arg(self))]
    /// The `rest` flag can be used on the first parameter to specify that all the arguments
    /// except the receiver appear in order.
    fn add(&mut self, x: i32, y: i32, z: i32) {
        self.x += x;
        self.y += y;
        self.z += z;
    }
}

fn main() {
    let mut v = Vec3 { x: 1, y: 2, z: 3 };

    run_callback_reverse(vec3::add, &mut v as *mut Vec3 as *mut _);

    assert_eq!(v, Vec3 { x: 2, y: 4, z: 6 })
}
