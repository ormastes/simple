//! Dynamic function pointer calls for Simple dynlib SFFI.
//!
//! These exports back `src/os/posix/dynlib_sffi.spl`. They intentionally use a
//! narrow integer ABI because the current Simple wrapper only exposes i64
//! arguments and i64 returns.

fn valid_fn_ptr(fn_ptr: i64) -> Option<usize> {
    if fn_ptr <= 0 {
        return None;
    }
    Some(fn_ptr as usize)
}

#[no_mangle]
pub extern "C" fn rt_dyncall_0(fn_ptr: i64) -> i64 {
    let Some(ptr) = valid_fn_ptr(fn_ptr) else {
        return -1;
    };
    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    func()
}

#[no_mangle]
pub extern "C" fn rt_dyncall_1(fn_ptr: i64, arg0: i64) -> i64 {
    let Some(ptr) = valid_fn_ptr(fn_ptr) else {
        return -1;
    };
    let func: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(ptr) };
    func(arg0)
}

#[no_mangle]
pub extern "C" fn rt_dyncall_2(fn_ptr: i64, arg0: i64, arg1: i64) -> i64 {
    let Some(ptr) = valid_fn_ptr(fn_ptr) else {
        return -1;
    };
    let func: extern "C" fn(i64, i64) -> i64 = unsafe { std::mem::transmute(ptr) };
    func(arg0, arg1)
}

/// Call the exact SimpleProviderQueryV1 discovery ABI.
///
/// This must remain separate from `rt_dyncall_2`: provider discovery returns
/// `int32_t` and accepts pointers to packed request/result buffers. Calling it
/// through the generic `fn(i64, i64) -> i64` type is incompatible-function-
/// type undefined behaviour even on targets where it appears to work.
#[no_mangle]
pub extern "C" fn rt_provider_query_v1_call(fn_ptr: i64, request_ptr: i64, result_ptr: i64) -> i32 {
    let Some(ptr) = valid_fn_ptr(fn_ptr) else {
        return -1;
    };
    if request_ptr <= 0 || result_ptr <= 0 {
        return -1;
    }
    let func: extern "C" fn(*const u8, *mut u8) -> i32 = unsafe { std::mem::transmute(ptr) };
    func(request_ptr as usize as *const u8, result_ptr as usize as *mut u8)
}

#[no_mangle]
pub extern "C" fn rt_dyncall_3(fn_ptr: i64, arg0: i64, arg1: i64, arg2: i64) -> i64 {
    let Some(ptr) = valid_fn_ptr(fn_ptr) else {
        return -1;
    };
    let func: extern "C" fn(i64, i64, i64) -> i64 = unsafe { std::mem::transmute(ptr) };
    func(arg0, arg1, arg2)
}

#[no_mangle]
pub extern "C" fn rt_dyncall_4(fn_ptr: i64, arg0: i64, arg1: i64, arg2: i64, arg3: i64) -> i64 {
    let Some(ptr) = valid_fn_ptr(fn_ptr) else {
        return -1;
    };
    let func: extern "C" fn(i64, i64, i64, i64) -> i64 = unsafe { std::mem::transmute(ptr) };
    func(arg0, arg1, arg2, arg3)
}

#[no_mangle]
pub extern "C" fn rt_dyncall_5(fn_ptr: i64, arg0: i64, arg1: i64, arg2: i64, arg3: i64, arg4: i64) -> i64 {
    let Some(ptr) = valid_fn_ptr(fn_ptr) else {
        return -1;
    };
    let func: extern "C" fn(i64, i64, i64, i64, i64) -> i64 = unsafe { std::mem::transmute(ptr) };
    func(arg0, arg1, arg2, arg3, arg4)
}

#[no_mangle]
pub extern "C" fn rt_dyncall_6(fn_ptr: i64, arg0: i64, arg1: i64, arg2: i64, arg3: i64, arg4: i64, arg5: i64) -> i64 {
    let Some(ptr) = valid_fn_ptr(fn_ptr) else {
        return -1;
    };
    let func: extern "C" fn(i64, i64, i64, i64, i64, i64) -> i64 = unsafe { std::mem::transmute(ptr) };
    func(arg0, arg1, arg2, arg3, arg4, arg5)
}

#[cfg(test)]
mod tests {
    use super::*;

    extern "C" fn zero() -> i64 {
        42
    }

    extern "C" fn sum2(a: i64, b: i64) -> i64 {
        a + b
    }

    extern "C" fn provider_query(request: *const u8, result: *mut u8) -> i32 {
        if request.is_null() || result.is_null() {
            return -9;
        }
        unsafe {
            *result = *request;
        }
        7
    }

    extern "C" fn sum6(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64) -> i64 {
        a + b + c + d + e + f
    }

    #[test]
    fn invalid_pointer_returns_negative() {
        assert_eq!(rt_dyncall_0(0), -1);
        assert_eq!(rt_dyncall_1(-1, 7), -1);
    }

    #[test]
    fn calls_zero_arg_function_pointer() {
        assert_eq!(rt_dyncall_0(zero as usize as i64), 42);
    }

    #[test]
    fn calls_two_arg_function_pointer() {
        assert_eq!(rt_dyncall_2(sum2 as usize as i64, 10, 32), 42);
    }

    #[test]
    fn calls_exact_provider_query_signature() {
        let request = [41u8; 44];
        let mut result = [0u8; 60];
        assert_eq!(
            rt_provider_query_v1_call(
                provider_query as usize as i64,
                request.as_ptr() as usize as i64,
                result.as_mut_ptr() as usize as i64,
            ),
            7
        );
        assert_eq!(result[0], 41);
        assert_eq!(rt_provider_query_v1_call(0, 1, 1), -1);
        assert_eq!(rt_provider_query_v1_call(provider_query as usize as i64, 0, 1), -1);
    }

    #[test]
    fn calls_six_arg_function_pointer() {
        assert_eq!(rt_dyncall_6(sum6 as usize as i64, 1, 2, 3, 4, 5, 6), 21);
    }
}
