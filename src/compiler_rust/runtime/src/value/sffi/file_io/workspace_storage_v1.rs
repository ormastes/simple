//! ABI twins explicitly lack the native retained storage capability. No path
//! mutation or process fallback may replace core-C enforcement readback.
use crate::value::RuntimeValue;
use crate::value::collections::rt_string_new;

#[no_mangle]
pub extern "C" fn rt_workspace_storage_open_v1(
    _kind: RuntimeValue, _parent: RuntimeValue, _leaf: RuntimeValue,
    _pool: RuntimeValue, _workspace: RuntimeValue, _quota: i64, _hard: i64,
    _policy: RuntimeValue,
) -> i64 { -95 }

#[no_mangle]
pub extern "C" fn rt_workspace_storage_recover_v1(
    _kind: RuntimeValue, _parent: RuntimeValue, _leaf: RuntimeValue,
    _pool: RuntimeValue, _workspace: RuntimeValue, _quota: i64, _hard: i64,
    _policy: RuntimeValue,
) -> i64 { -95 }

#[no_mangle]
pub extern "C" fn rt_workspace_storage_observe_v1(_token: i64) -> RuntimeValue {
    unsafe { rt_string_new(b"".as_ptr(), 0) }
}
#[no_mangle]
pub extern "C" fn rt_workspace_storage_release_if_absent_v1(_token: i64) -> i64 { -95 }
#[no_mangle]
pub extern "C" fn rt_workspace_storage_forget_released_v1(_token: i64) -> i64 { -95 }

#[no_mangle]
pub extern "C" fn rt_linux_container_user_open_v1(_pid:i64,_cgroup:RuntimeValue,_binding:RuntimeValue)->i64{-95}
#[no_mangle]
pub extern "C" fn rt_linux_container_user_observe_v1(_token:i64,_binding:RuntimeValue)->RuntimeValue{
    unsafe {rt_string_new(b"".as_ptr(),0)}
}
#[no_mangle]
pub extern "C" fn rt_linux_container_user_close_v1(_token:i64,_binding:RuntimeValue)->i64{-95}
