//! Tests for async/future functionality

use super::{
    rt_future_all, rt_future_await, rt_future_is_ready, rt_future_new, rt_future_race,
    rt_future_resolve,
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
    let future = rt_future_new(return_value as u64, RuntimeValue::from_int(123));

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
    let future = rt_future_new(increment_counter as u64, RuntimeValue::NIL);

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

    let future = rt_future_new(double_int as u64, RuntimeValue::from_int(21));

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

    let future = rt_future_new(return_value as u64, RuntimeValue::from_int(100));

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
    // Try to await a non-future value
    let not_a_future = RuntimeValue::from_int(42);

    let result = rt_future_await(not_a_future);

    // Should return NIL for invalid input
    assert!(result.is_nil());
}
