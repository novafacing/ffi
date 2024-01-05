// Copyright (C) 2024 Rowan Hart
// SPDX-License-Identifier: Apache-2.0

use ffi::ffi;

extern "C" fn run_callback(
    callback: extern "C" fn(*mut std::ffi::c_void, i32, i32, i32) -> i32,
    data: *mut std::ffi::c_void,
) -> i32 {
    callback(data, 1, 2, 3)
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
}

fn main() {
    let mut v = Vec3 { x: 1, y: 2, z: 3 };

    run_callback(vec3::add, &mut v as *mut Vec3 as *mut _);

    assert_eq!(v, Vec3 { x: 2, y: 4, z: 6 })
}
