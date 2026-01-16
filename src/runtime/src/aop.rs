//! Runtime support for around advice and proceed enforcement (AOP).

use crate::value::RuntimeValue;

/// Target function signature for around advice chains.
pub type AopTargetFn = extern "C" fn(argc: u64, argv: *const RuntimeValue) -> RuntimeValue;

/// Around advice function signature.
pub type AopAroundFn = extern "C" fn(ctx: *mut ProceedContext, argc: u64, argv: *const RuntimeValue) -> RuntimeValue;

/// Proceed context passed to around advice.
#[repr(C)]
pub struct ProceedContext {
    target: AopTargetFn,
    advices: *const AopAroundFn,
    advice_len: u64,
    argc: u64,
    argv: *const RuntimeValue,
    next_index: u64,
    proceed_called: bool,
}

impl ProceedContext {
    fn new(
        target: AopTargetFn,
        advices: *const AopAroundFn,
        advice_len: u64,
        argc: u64,
        argv: *const RuntimeValue,
    ) -> Self {
        Self {
            target,
            advices,
            advice_len,
            argc,
            argv,
            next_index: 0,
            proceed_called: false,
        }
    }
}

unsafe fn invoke_advice(ctx: &mut ProceedContext, advice: AopAroundFn) -> RuntimeValue {
    ctx.proceed_called = false;
    let result = advice(ctx as *mut ProceedContext, ctx.argc, ctx.argv);
    if !ctx.proceed_called {
        panic!("around advice did not call proceed() exactly once");
    }
    result
}

unsafe fn call_next(ctx: &mut ProceedContext) -> RuntimeValue {
    if ctx.next_index < ctx.advice_len {
        let advice = *ctx.advices.add(ctx.next_index as usize);
        ctx.next_index += 1;
        invoke_advice(ctx, advice)
    } else {
        (ctx.target)(ctx.argc, ctx.argv)
    }
}

/// Invoke a chain of around advices and then the target function.
///
/// Advice order is outermost-first (advices[0] wraps advices[1], etc.).
#[no_mangle]
pub extern "C" fn rt_aop_invoke_around(
    target: AopTargetFn,
    advices: *const AopAroundFn,
    advice_len: u64,
    argc: u64,
    argv: *const RuntimeValue,
) -> RuntimeValue {
    if advice_len > 0 && advices.is_null() {
        panic!("around advice list pointer is null");
    }

    let mut ctx = ProceedContext::new(target, advices, advice_len, argc, argv);
    unsafe { call_next(&mut ctx) }
}

/// Continue to the next advice or the target function.
///
/// This must be called exactly once per advice invocation.
#[no_mangle]
pub unsafe extern "C" fn rt_aop_proceed(ctx: *mut ProceedContext) -> RuntimeValue {
    if ctx.is_null() {
        panic!("around proceed() called with null context");
    }
    let ctx = &mut *ctx;
    if ctx.proceed_called {
        panic!("around advice called proceed() more than once");
    }
    ctx.proceed_called = true;
    call_next(ctx)
}
