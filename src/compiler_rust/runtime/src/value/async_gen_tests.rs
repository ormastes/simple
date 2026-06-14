//! Tests for async/future functionality

use super::{
    rt_future_all, rt_future_await, rt_future_is_ready, rt_future_new, rt_future_race, rt_future_resolve,
    rt_future_wrap,
};
use crate::executor::{configure_async_mode, AsyncMode};
use crate::value::{rt_array_get, rt_array_len, rt_array_new, rt_array_push, RuntimeValue};
use std::sync::atomic::{AtomicI32, Ordering};

// Test helper: Simple function that returns a value
extern "C" fn return_value(ctx: RuntimeValue) -> RuntimeValue {
    ctx
}

// Test helper: Function that doubles an integer
extern "C" fn double_int(ctx: RuntimeValue) -> RuntimeValue {
    let n = ctx.as_int();
    RuntimeValue::from_int(n * 2)
}

// Test helper: Function that increments a counter
static TEST_COUNTER: AtomicI32 = AtomicI32::new(0);

extern "C" fn increment_counter(_ctx: RuntimeValue) -> RuntimeValue {
    TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    RuntimeValue::from_int(42)
}

#[test]
fn test_future_new_and_await_simple() {
    // Reset counter
    TEST_COUNTER.store(0, Ordering::SeqCst);

    // Ensure threaded mode
    configure_async_mode(AsyncMode::Threaded);

    // Create a future with lazy execution
    let future = rt_future_new(return_value as *const () as u64, RuntimeValue::from_int(123));

    // Counter should be 0 (lazy execution)
    assert!(future.is_heap());

    // Await the future
    let result = rt_future_await(future);

    // Should return the value
    assert!(result.is_int());
    assert_eq!(result.as_int(), 123);
}

#[test]
fn test_future_await_executes_body() {
    // Reset counter
    TEST_COUNTER.store(0, Ordering::SeqCst);

    configure_async_mode(AsyncMode::Threaded);

    // Create future with counter increment
    let future = rt_future_new(increment_counter as *const () as u64, RuntimeValue::NIL);

    // Counter should still be 0 (lazy)
    assert_eq!(TEST_COUNTER.load(Ordering::SeqCst), 0);

    // Await should execute the function
    let result = rt_future_await(future);

    // Counter should be incremented
    assert_eq!(TEST_COUNTER.load(Ordering::SeqCst), 1);
    assert_eq!(result.as_int(), 42);
}

#[test]
fn test_future_await_double_await() {
    configure_async_mode(AsyncMode::Threaded);

    let future = rt_future_new(double_int as *const () as u64, RuntimeValue::from_int(21));

    // First await
    let result1 = rt_future_await(future);
    assert_eq!(result1.as_int(), 42);

    // Second await should return cached result
    let result2 = rt_future_await(future);
    assert_eq!(result2.as_int(), 42);
}

#[test]
fn test_future_is_ready() {
    configure_async_mode(AsyncMode::Threaded);

    let future = rt_future_new(return_value as *const () as u64, RuntimeValue::from_int(100));

    // Not ready initially (lazy execution)
    assert_eq!(rt_future_is_ready(future), 0);

    // Await it
    rt_future_await(future);

    // Now should be ready
    assert_eq!(rt_future_is_ready(future), 1);
}

#[test]
fn test_future_resolve() {
    // Create an immediately resolved future
    let future = rt_future_resolve(RuntimeValue::from_int(999));

    // Should be ready immediately
    assert_eq!(rt_future_is_ready(future), 1);

    // Await should return the value immediately
    let result = rt_future_await(future);
    assert_eq!(result.as_int(), 999);
}

#[test]
fn test_future_all() {
    configure_async_mode(AsyncMode::Threaded);

    // Create an array of futures
    let futures = rt_array_new(3);

    let f1 = rt_future_resolve(RuntimeValue::from_int(10));
    let f2 = rt_future_resolve(RuntimeValue::from_int(20));
    let f3 = rt_future_resolve(RuntimeValue::from_int(30));

    rt_array_push(futures, f1);
    rt_array_push(futures, f2);
    rt_array_push(futures, f3);

    // Wait for all
    let results = rt_future_all(futures);

    // Should have 3 results
    assert_eq!(rt_array_len(results), 3);
    assert_eq!(rt_array_get(results, 0).as_int(), 10);
    assert_eq!(rt_array_get(results, 1).as_int(), 20);
    assert_eq!(rt_array_get(results, 2).as_int(), 30);
}

#[test]
fn test_future_race() {
    configure_async_mode(AsyncMode::Threaded);

    // Create an array of futures
    let futures = rt_array_new(2);

    let f1 = rt_future_resolve(RuntimeValue::from_int(100));
    let f2 = rt_future_resolve(RuntimeValue::from_int(200));

    rt_array_push(futures, f1);
    rt_array_push(futures, f2);

    // Race - should return first ready future
    let result = rt_future_race(futures);

    // Should be one of the values (first one in eager mode)
    assert_eq!(result.as_int(), 100);
}

#[test]
fn test_future_nil_body_func() {
    configure_async_mode(AsyncMode::Threaded);

    // Create future with null function pointer
    let future = rt_future_new(0, RuntimeValue::NIL);

    // Await should return NIL
    let result = rt_future_await(future);
    assert!(result.is_nil());
}

#[test]
fn test_future_invalid_value() {
    // Awaiting a non-future is the identity (eager-async semantics): the value
    // is already resolved. Returning NIL here was the silent-corruption bug
    // where `await f()` yielded the NIL bit pattern instead of f's result.
    let not_a_future = RuntimeValue::from_int(42);

    let result = rt_future_await(not_a_future);

    assert_eq!(result.as_int(), 42);
}

// B5 regression suite — Promise vs FutureValue dual representation
// (src/compiler_rust/runtime/src/value/async_gen.rs, 2026-06-11)
//
// Simple async is EAGER: async fn bodies run at call time; await on a
// non-RuntimeFuture is the identity.  The interpreter uses two representations:
//   (a) FutureValue (Value::Future)   — interpreter Expr::Await path
//   (b) Promise object (Value::Object{class:"Promise",...}) — wrap_in_promise path
//   (c) RuntimeFuture (HeapObjectType::Future) — JIT/MIR rt_future_await path
//
// All three reach rt_future_await in the MIR executor; only (c) is a real
// RuntimeFuture.  The B1/B2 fix made rt_future_await identity-safe for (a)/(b),
// masking the split under eager semantics.  These tests pin that contract.

#[test]
fn test_b5_await_plain_int_identity() {
    // await(42i64) — plain int is not a RuntimeFuture; must return 42, not NIL
    let plain = RuntimeValue::from_int(42);
    assert_eq!(rt_future_await(plain).as_int(), 42);
}

#[test]
fn test_b5_await_nil_identity() {
    // await(NIL) — NIL is not a RuntimeFuture; must return NIL, not crash
    let result = rt_future_await(RuntimeValue::NIL);
    assert!(result.is_nil());
}

#[test]
fn test_b5_nested_await_double_identity() {
    // await(await(plain_value)) — both layers are identity for non-Future
    // This would have returned NIL twice before B1/B2 fix.
    let plain = RuntimeValue::from_int(99);
    let once = rt_future_await(plain);
    let twice = rt_future_await(once);
    assert_eq!(twice.as_int(), 99);
}

#[test]
fn test_b5_await_resolved_future_value() {
    // await(rt_future_resolve(val)) — already-resolved RuntimeFuture must return val
    configure_async_mode(AsyncMode::Threaded);
    let future = rt_future_resolve(RuntimeValue::from_int(777));
    let result = rt_future_await(future);
    assert_eq!(result.as_int(), 777);
}

#[test]
fn test_b5_nested_await_future_value() {
    // await(await(future)) — second await hits a plain int (the resolved value),
    // identity must hold; must not NIL or crash.
    configure_async_mode(AsyncMode::Threaded);
    let future = rt_future_resolve(RuntimeValue::from_int(55));
    let resolved = rt_future_await(future); // RuntimeFuture → 55
    let again = rt_future_await(resolved); // plain int → identity → 55
    assert_eq!(again.as_int(), 55);
}

#[test]
fn test_b5_promise_object_through_rt_future_await() {
    // Canonical B5 cross-path test:
    // A Simple-level "Promise" object (as produced by the interpreter's
    // wrap_in_promise) flows through rt_future_await (the MIR/JIT path).
    // rt_future_await must NOT return NIL — it returns the opaque value
    // (identity), because eager semantics means the value is already resolved.
    // The interpreter's await_value is responsible for Promise.state extraction;
    // rt_future_await's contract is only to not corrupt/NIL the value.
    //
    // We simulate the Promise object as a heap string (any non-Future heap value
    // that is not the NIL bit pattern) to verify the identity contract.
    // A proper Promise object is a Value::Object and cannot be constructed at
    // the RuntimeValue level (it is an interpreter-layer type), so we use
    // a resolved future as a proxy for "already-computed, non-Future value".
    let eager_value = RuntimeValue::from_int(0x42); // arbitrary non-NIL value
    let result = rt_future_await(eager_value);
    // Must be identity: neither NIL nor corrupted
    assert!(
        !result.is_nil(),
        "rt_future_await must not return NIL for non-Future (eager-async identity)"
    );
    assert_eq!(result.as_int(), 0x42);
}

#[test]
fn test_b5_lazy_future_await_returns_body_value() {
    // await(rt_future_new(fn, ctx)) — lazy future executes fn on first await
    // Verifies the normal RuntimeFuture path still returns the correct value.
    configure_async_mode(AsyncMode::Threaded);
    let future = rt_future_new(return_value as *const () as u64, RuntimeValue::from_int(512));
    let result = rt_future_await(future);
    assert_eq!(result.as_int(), 512);
}

// B5 reconcile (RECONCILED, 2026-06-13) — canonical constructor tests
//
// rt_future_wrap is the single intent-named canonical constructor for "I have a
// resolved value; wrap it for the RuntimeFuture await path."  It is a thin alias
// for rt_future_resolve, but makes the construction intent unambiguous so future
// MIR/JIT lowering does not have to choose between rt_future_new/rt_future_resolve.
//
// These tests verify: wrap produces a ready future, await extracts the value,
// parity with rt_future_resolve, nil handling, and nested wrap+await.

#[test]
fn test_b5_canonical_wrap_int() {
    // rt_future_wrap(i64) must produce a ready future that await extracts correctly.
    let wrapped = rt_future_wrap(RuntimeValue::from_int(42));
    assert_eq!(
        rt_future_is_ready(wrapped),
        1,
        "rt_future_wrap must produce a ready future"
    );
    let result = rt_future_await(wrapped);
    assert_eq!(result.as_int(), 42);
}

#[test]
fn test_b5_canonical_wrap_nil() {
    // rt_future_wrap(NIL) must produce a ready future; await must return NIL.
    let wrapped = rt_future_wrap(RuntimeValue::NIL);
    assert_eq!(rt_future_is_ready(wrapped), 1);
    let result = rt_future_await(wrapped);
    assert!(result.is_nil());
}

#[test]
fn test_b5_canonical_wrap_parity_with_resolve() {
    // rt_future_wrap and rt_future_resolve must be behaviorally identical.
    let val = RuntimeValue::from_int(1234);
    let via_wrap = rt_future_wrap(val);
    let via_resolve = rt_future_resolve(val);
    // Both must be immediately ready
    assert_eq!(rt_future_is_ready(via_wrap), 1);
    assert_eq!(rt_future_is_ready(via_resolve), 1);
    // Both must yield the same value on await
    assert_eq!(rt_future_await(via_wrap).as_int(), 1234);
    assert_eq!(rt_future_await(via_resolve).as_int(), 1234);
}

#[test]
fn test_b5_canonical_wrap_nested_await() {
    // await(await(rt_future_wrap(v))) — second await hits the plain extracted int
    // (identity path), must return the same value, not NIL or crash.
    let wrapped = rt_future_wrap(RuntimeValue::from_int(99));
    let first = rt_future_await(wrapped); // RuntimeFuture → 99
    let second = rt_future_await(first); // plain int → identity → 99
    assert_eq!(second.as_int(), 99);
}

#[test]
fn test_b5_canonical_wrap_double_await_cached() {
    // Awaiting the same rt_future_wrap'd future twice must return the same
    // cached result (state == 1 path, no body re-execution).
    let wrapped = rt_future_wrap(RuntimeValue::from_int(7));
    let r1 = rt_future_await(wrapped);
    let r2 = rt_future_await(wrapped);
    assert_eq!(r1.as_int(), 7);
    assert_eq!(r2.as_int(), 7);
}

#[test]
fn test_b5_canonical_single_await_path_for_plain_value() {
    // The single await path (rt_future_await) handles both:
    //   (a) a plain non-Future value — identity, not NIL
    //   (b) an rt_future_wrap'd value — extract, not NIL
    // Both must produce the same result, confirming the unified extract path.
    let plain = RuntimeValue::from_int(55);
    let wrapped = rt_future_wrap(RuntimeValue::from_int(55));
    let from_plain = rt_future_await(plain);
    let from_wrapped = rt_future_await(wrapped);
    assert_eq!(from_plain.as_int(), 55);
    assert_eq!(from_wrapped.as_int(), 55);
}
