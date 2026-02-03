//! Runtime support for around advice and proceed enforcement (AOP).

use crate::value::RuntimeValue;
use std::cell::Cell;
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};

/// Target function signature for around advice chains.
pub type AopTargetFn = extern "C" fn(argc: u64, argv: *const RuntimeValue) -> RuntimeValue;

/// Around advice function signature.
pub type AopAroundFn = extern "C" fn(ctx: *mut ProceedContext, argc: u64, argv: *const RuntimeValue) -> RuntimeValue;

// Thread-local storage for panic payload that needs to cross FFI boundary
thread_local! {
    static PENDING_PANIC: Cell<Option<Box<dyn std::any::Any + Send + 'static>>> = const { Cell::new(None) };
}

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

    // Check if a panic was stored during the advice execution
    let pending = PENDING_PANIC.with(|p| p.take());
    if let Some(payload) = pending {
        resume_unwind(payload);
    }

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

/// Internal implementation that can panic - used for testing
fn invoke_around_inner(
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

/// Invoke a chain of around advices and then the target function.
///
/// Advice order is outermost-first (advices[0] wraps advices[1], etc.).
///
/// This is the FFI-safe version that catches panics and re-throws them
/// after leaving the extern "C" boundary.
#[no_mangle]
pub extern "C" fn rt_aop_invoke_around(
    target: AopTargetFn,
    advices: *const AopAroundFn,
    advice_len: u64,
    argc: u64,
    argv: *const RuntimeValue,
) -> RuntimeValue {
    // Wrap in catch_unwind to handle panics safely at FFI boundary
    let result = catch_unwind(AssertUnwindSafe(|| {
        invoke_around_inner(target, advices, advice_len, argc, argv)
    }));

    match result {
        Ok(val) => val,
        Err(payload) => {
            // Re-throw the panic now that we're returning to Rust code
            resume_unwind(payload);
        }
    }
}

/// Continue to the next advice or the target function.
///
/// This must be called exactly once per advice invocation.
#[no_mangle]
pub unsafe extern "C" fn rt_aop_proceed(ctx: *mut ProceedContext) -> RuntimeValue {
    // Wrap the panic-able code in catch_unwind
    let result = catch_unwind(AssertUnwindSafe(|| {
        if ctx.is_null() {
            panic!("around proceed() called with null context");
        }
        let ctx = &mut *ctx;
        if ctx.proceed_called {
            panic!("around advice called proceed() more than once");
        }
        ctx.proceed_called = true;
        call_next(ctx)
    }));

    match result {
        Ok(val) => val,
        Err(payload) => {
            // Store the panic to be re-thrown after leaving extern "C" callbacks
            PENDING_PANIC.with(|p| p.set(Some(payload)));
            RuntimeValue::from_int(0) // Dummy return, panic will be re-thrown
        }
    }
}

#[cfg(test)]
pub use test_helpers::*;

#[cfg(test)]
mod test_helpers {
    use super::*;

    /// Test-only function that bypasses FFI and allows panics to propagate normally
    pub fn rt_aop_invoke_around_test(
        target: AopTargetFn,
        advices: *const AopAroundFn,
        advice_len: u64,
        argc: u64,
        argv: *const RuntimeValue,
    ) -> RuntimeValue {
        invoke_around_inner(target, advices, advice_len, argc, argv)
    }
}
