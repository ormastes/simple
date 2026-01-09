use crate::aop::{rt_aop_invoke_around, rt_aop_proceed, ProceedContext};
use crate::value::RuntimeValue;

extern "C" fn target_sum(argc: u64, argv: *const RuntimeValue) -> RuntimeValue {
    if argc == 0 || argv.is_null() {
        return RuntimeValue::from_int(0);
    }
    let args = unsafe { std::slice::from_raw_parts(argv, argc as usize) };
    let mut sum = 0i64;
    for arg in args {
        sum += arg.as_int();
    }
    RuntimeValue::from_int(sum)
}

extern "C" fn advice_add_one(
    ctx: *mut ProceedContext,
    _argc: u64,
    _argv: *const RuntimeValue,
) -> RuntimeValue {
    let result = unsafe { rt_aop_proceed(ctx) };
    RuntimeValue::from_int(result.as_int() + 1)
}

extern "C" fn advice_mul_two(
    ctx: *mut ProceedContext,
    _argc: u64,
    _argv: *const RuntimeValue,
) -> RuntimeValue {
    let result = unsafe { rt_aop_proceed(ctx) };
    RuntimeValue::from_int(result.as_int() * 2)
}

extern "C" fn advice_no_proceed(
    _ctx: *mut ProceedContext,
    _argc: u64,
    _argv: *const RuntimeValue,
) -> RuntimeValue {
    RuntimeValue::from_int(0)
}

extern "C" fn advice_double_proceed(
    ctx: *mut ProceedContext,
    _argc: u64,
    _argv: *const RuntimeValue,
) -> RuntimeValue {
    let _ = unsafe { rt_aop_proceed(ctx) };
    let _ = unsafe { rt_aop_proceed(ctx) };
    RuntimeValue::from_int(0)
}

#[test]
fn around_chain_applies_outermost_first() {
    let args = vec![RuntimeValue::from_int(1), RuntimeValue::from_int(2)];
    let advices = vec![advice_add_one as _, advice_mul_two as _];

    // Test with small stack-safe operations
    let result = rt_aop_invoke_around(
        target_sum,
        advices.as_ptr(),
        advices.len() as u64,
        args.len() as u64,
        args.as_ptr(),
    );
    // Expected: sum(1,2)=3 -> mul_two(3)=6 -> add_one(6)=7
    assert_eq!(result.as_int(), 7);
}

#[test]
#[should_panic(expected = "around advice did not call proceed() exactly once")]
fn around_requires_proceed() {
    let args = vec![RuntimeValue::from_int(5)];
    let advices = vec![advice_no_proceed as _];
    let _ = rt_aop_invoke_around(
        target_sum,
        advices.as_ptr(),
        advices.len() as u64,
        args.len() as u64,
        args.as_ptr(),
    );
}

#[test]
#[should_panic(expected = "around advice called proceed() more than once")]
fn around_rejects_double_proceed() {
    let args = vec![RuntimeValue::from_int(5)];
    let advices = vec![advice_double_proceed as _];
    let _ = rt_aop_invoke_around(
        target_sum,
        advices.as_ptr(),
        advices.len() as u64,
        args.len() as u64,
        args.as_ptr(),
    );
}
