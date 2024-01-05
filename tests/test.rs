// Copyright (C) 2024 Rowan Hart
// SPDX-License-Identifier: Apache-2.0

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
    fn test_forward_rest(&mut self, x: i32, y: i32, z: i32) -> i32 {
        self.x += x;
        self.y += y;
        self.z += z;
        self.x + self.y + self.z
    }

    #[ffi(arg(self), arg(), arg(), arg())]
    fn test_forward_each(&mut self, x: i32, y: i32, z: i32) -> i32 {
        self.x += x;
        self.y += y;
        self.z += z;
        self.x + self.y + self.z
    }

    #[ffi(expect, arg(self), arg(rest))]
    fn test_forward_expect(&mut self, x: i32, y: i32, z: i32) -> anyhow::Result<i32> {
        self.x += x;
        self.y += y;
        self.z += z;
        Ok(self.x + self.y + self.z)
    }

    #[ffi(arg(rest), arg(self))]
    fn test_reverse_rest(&mut self, x: i32, y: i32, z: i32) -> i32 {
        self.x += x;
        self.y += y;
        self.z += z;
        self.x + self.y + self.z
    }

    #[ffi(arg(), arg(), arg(), arg(self))]
    fn test_reverse_each(&mut self, x: i32, y: i32, z: i32) -> i32 {
        self.x += x;
        self.y += y;
        self.z += z;
        self.x + self.y + self.z
    }

    #[ffi(expect, arg(rest), arg(self))]
    fn test_reverse_expect(&mut self, x: i32, y: i32, z: i32) -> anyhow::Result<i32> {
        self.x += x;
        self.y += y;
        self.z += z;
        Ok(self.x + self.y + self.z)
    }
}

#[test]
fn forward_rest() -> anyhow::Result<()> {
    let mut v = Vec3 { x: 1, y: 2, z: 3 };

    assert_eq!(
        run_callback(vec3::test_forward_rest, &mut v as *mut Vec3 as *mut _),
        12
    );

    Ok(())
}

#[test]
fn forward_each() -> anyhow::Result<()> {
    let mut v = Vec3 { x: 1, y: 2, z: 3 };

    assert_eq!(
        run_callback(vec3::test_forward_each, &mut v as *mut Vec3 as *mut _),
        12
    );

    Ok(())
}

#[test]
fn forward_expect() -> anyhow::Result<()> {
    let mut v = Vec3 { x: 1, y: 2, z: 3 };

    assert_eq!(
        run_callback(vec3::test_forward_expect, &mut v as *mut Vec3 as *mut _),
        12
    );

    Ok(())
}

#[test]
fn reverse_rest() -> anyhow::Result<()> {
    let mut v = Vec3 { x: 1, y: 2, z: 3 };

    assert_eq!(
        run_callback_reverse(vec3::test_reverse_rest, &mut v as *mut Vec3 as *mut _),
        12
    );

    Ok(())
}

#[test]
fn reverse_each() -> anyhow::Result<()> {
    let mut v = Vec3 { x: 1, y: 2, z: 3 };

    assert_eq!(
        run_callback_reverse(vec3::test_reverse_each, &mut v as *mut Vec3 as *mut _),
        12
    );

    Ok(())
}

#[test]
fn reverse_expect() -> anyhow::Result<()> {
    let mut v = Vec3 { x: 1, y: 2, z: 3 };

    assert_eq!(
        run_callback_reverse(vec3::test_reverse_expect, &mut v as *mut Vec3 as *mut _),
        12
    );

    Ok(())
}
