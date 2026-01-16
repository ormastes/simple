//! Tests for generator functionality

use super::{
    rt_generator_get_ctx, rt_generator_get_state, rt_generator_load_slot, rt_generator_mark_done, rt_generator_new,
    rt_generator_next, rt_generator_set_state, rt_generator_store_slot,
};
use crate::value::RuntimeValue;
use std::sync::atomic::{AtomicI32, Ordering};

// Test helper: Counter for tracking generator execution
static GENERATOR_COUNTER: AtomicI32 = AtomicI32::new(0);

// Test helper: Simple generator that yields sequential values
extern "C" fn simple_yielder(gen: RuntimeValue) -> RuntimeValue {
    use super::{rt_generator_get_state, rt_generator_mark_done, rt_generator_set_state};

    let state = rt_generator_get_state(gen);

    match state {
        0 => {
            // First yield: return 10
            rt_generator_set_state(gen, 1);
            RuntimeValue::from_int(10)
        }
        1 => {
            // Second yield: return 20
            rt_generator_set_state(gen, 2);
            RuntimeValue::from_int(20)
        }
        2 => {
            // Third yield: return 30
            rt_generator_set_state(gen, 3);
            RuntimeValue::from_int(30)
        }
        _ => {
            // Done
            rt_generator_mark_done(gen);
            RuntimeValue::NIL
        }
    }
}

// Test helper: Generator that uses slot storage
extern "C" fn slot_based_generator(gen: RuntimeValue) -> RuntimeValue {
    use super::{
        rt_generator_get_state, rt_generator_load_slot, rt_generator_mark_done, rt_generator_set_state,
        rt_generator_store_slot,
    };

    let state = rt_generator_get_state(gen);

    match state {
        0 => {
            // Initialize counter in slot 0
            rt_generator_store_slot(gen, 0, RuntimeValue::from_int(0));
            rt_generator_set_state(gen, 1);
            RuntimeValue::from_int(0)
        }
        1 | 2 | 3 => {
            // Increment counter and yield
            let counter = rt_generator_load_slot(gen, 0);
            let new_val = counter.as_int() + 1;
            rt_generator_store_slot(gen, 0, RuntimeValue::from_int(new_val));
            rt_generator_set_state(gen, state + 1);
            RuntimeValue::from_int(new_val)
        }
        _ => {
            rt_generator_mark_done(gen);
            RuntimeValue::NIL
        }
    }
}

// Test helper: Generator that uses context
extern "C" fn context_based_generator(gen: RuntimeValue) -> RuntimeValue {
    use super::{rt_generator_get_ctx, rt_generator_get_state, rt_generator_mark_done, rt_generator_set_state};

    let state = rt_generator_get_state(gen);
    let ctx = rt_generator_get_ctx(gen);

    if state < 3 && ctx.is_int() {
        let value = ctx.as_int() + state;
        rt_generator_set_state(gen, state + 1);
        RuntimeValue::from_int(value)
    } else {
        rt_generator_mark_done(gen);
        RuntimeValue::NIL
    }
}

// Test helper: Generator that counts executions
extern "C" fn counting_generator(_gen: RuntimeValue) -> RuntimeValue {
    let count = GENERATOR_COUNTER.fetch_add(1, Ordering::SeqCst);
    RuntimeValue::from_int(count as i64)
}

#[test]
fn test_generator_new() {
    let gen = rt_generator_new(
        simple_yielder as *const () as u64,
        10, // 10 slots
        RuntimeValue::NIL,
    );

    assert!(gen.is_heap());
    assert_eq!(rt_generator_get_state(gen), 0);
}

#[test]
fn test_generator_simple_yield_sequence() {
    let gen = rt_generator_new(simple_yielder as *const () as u64, 0, RuntimeValue::NIL);

    // First next: state 0 -> 1, yield 10
    let val1 = rt_generator_next(gen);
    assert_eq!(val1.as_int(), 10);
    assert_eq!(rt_generator_get_state(gen), 1);

    // Second next: state 1 -> 2, yield 20
    let val2 = rt_generator_next(gen);
    assert_eq!(val2.as_int(), 20);
    assert_eq!(rt_generator_get_state(gen), 2);

    // Third next: state 2 -> 3, yield 30
    let val3 = rt_generator_next(gen);
    assert_eq!(val3.as_int(), 30);
    assert_eq!(rt_generator_get_state(gen), 3);

    // Fourth next: exhausted, return NIL
    let val4 = rt_generator_next(gen);
    assert!(val4.is_nil());
}

#[test]
fn test_generator_slot_storage() {
    let gen = rt_generator_new(
        slot_based_generator as *const () as u64,
        10, // Need slots for storage
        RuntimeValue::NIL,
    );

    // First yield: initialize counter to 0
    let val0 = rt_generator_next(gen);
    assert_eq!(val0.as_int(), 0);

    // Next yields: increment counter
    let val1 = rt_generator_next(gen);
    assert_eq!(val1.as_int(), 1);

    let val2 = rt_generator_next(gen);
    assert_eq!(val2.as_int(), 2);

    let val3 = rt_generator_next(gen);
    assert_eq!(val3.as_int(), 3);

    // Verify slot contains the final value
    let slot_val = rt_generator_load_slot(gen, 0);
    assert_eq!(slot_val.as_int(), 3);
}

#[test]
fn test_generator_context() {
    // Create generator with context value 100
    let gen = rt_generator_new(
        context_based_generator as *const () as u64,
        0,
        RuntimeValue::from_int(100),
    );

    // Verify context is accessible
    let ctx = rt_generator_get_ctx(gen);
    assert!(ctx.is_int());
    assert_eq!(ctx.as_int(), 100);

    // Yields should be: 100+0=100, 100+1=101, 100+2=102
    let val0 = rt_generator_next(gen);
    assert_eq!(val0.as_int(), 100);

    let val1 = rt_generator_next(gen);
    assert_eq!(val1.as_int(), 101);

    let val2 = rt_generator_next(gen);
    assert_eq!(val2.as_int(), 102);

    // Should be exhausted
    let val3 = rt_generator_next(gen);
    assert!(val3.is_nil());
}

#[test]
fn test_generator_state_manipulation() {
    let gen = rt_generator_new(simple_yielder as *const () as u64, 0, RuntimeValue::NIL);

    // Initial state is 0
    assert_eq!(rt_generator_get_state(gen), 0);

    // Manually set state
    rt_generator_set_state(gen, 5);
    assert_eq!(rt_generator_get_state(gen), 5);

    // Negative state should be clamped to 0
    rt_generator_set_state(gen, -10);
    assert_eq!(rt_generator_get_state(gen), 0);
}

#[test]
fn test_generator_slot_operations() {
    let gen = rt_generator_new(
        simple_yielder as *const () as u64,
        5, // 5 slots
        RuntimeValue::NIL,
    );

    // Store values in different slots
    rt_generator_store_slot(gen, 0, RuntimeValue::from_int(10));
    rt_generator_store_slot(gen, 1, RuntimeValue::from_int(20));
    rt_generator_store_slot(gen, 2, RuntimeValue::from_int(30));

    // Load and verify
    assert_eq!(rt_generator_load_slot(gen, 0).as_int(), 10);
    assert_eq!(rt_generator_load_slot(gen, 1).as_int(), 20);
    assert_eq!(rt_generator_load_slot(gen, 2).as_int(), 30);

    // Uninitialized slot should return NIL
    let uninitialized = rt_generator_load_slot(gen, 4);
    assert!(uninitialized.is_nil());

    // Out of bounds slot should return NIL
    let out_of_bounds = rt_generator_load_slot(gen, 100);
    assert!(out_of_bounds.is_nil());
}

#[test]
fn test_generator_slot_auto_resize() {
    let gen = rt_generator_new(
        simple_yielder as *const () as u64,
        2, // Start with only 2 slots
        RuntimeValue::NIL,
    );

    // Store beyond initial capacity (should auto-resize)
    rt_generator_store_slot(gen, 10, RuntimeValue::from_int(999));

    // Should be able to load it
    let val = rt_generator_load_slot(gen, 10);
    assert_eq!(val.as_int(), 999);
}

#[test]
fn test_generator_mark_done() {
    let gen = rt_generator_new(simple_yielder as *const () as u64, 0, RuntimeValue::NIL);

    // Generator starts not done
    let val1 = rt_generator_next(gen);
    assert!(!val1.is_nil());

    // Manually mark as done
    rt_generator_mark_done(gen);

    // Should return NIL after being marked done
    let val2 = rt_generator_next(gen);
    assert!(val2.is_nil());
}

#[test]
fn test_generator_nil_body_func() {
    let gen = rt_generator_new(
        0, // Null function pointer
        0,
        RuntimeValue::NIL,
    );

    // Should return NIL when body_func is null
    let result = rt_generator_next(gen);
    assert!(result.is_nil());
}

#[test]
fn test_generator_invalid_value() {
    // Try to call generator functions on a non-generator value
    let not_a_gen = RuntimeValue::from_int(42);

    // All operations should return safe defaults
    assert_eq!(rt_generator_get_state(not_a_gen), 0);
    assert!(rt_generator_load_slot(not_a_gen, 0).is_nil());
    assert!(rt_generator_get_ctx(not_a_gen).is_nil());
    assert!(rt_generator_next(not_a_gen).is_nil());

    // These should not crash
    rt_generator_set_state(not_a_gen, 5);
    rt_generator_store_slot(not_a_gen, 0, RuntimeValue::from_int(100));
    rt_generator_mark_done(not_a_gen);
}

#[test]
fn test_generator_negative_slot_index() {
    let gen = rt_generator_new(simple_yielder as *const () as u64, 10, RuntimeValue::NIL);

    // Negative index should be ignored
    rt_generator_store_slot(gen, -5, RuntimeValue::from_int(100));
    let val = rt_generator_load_slot(gen, -5);
    assert!(val.is_nil());
}

#[test]
fn test_generator_execution_count() {
    // Reset counter
    GENERATOR_COUNTER.store(0, Ordering::SeqCst);

    let gen = rt_generator_new(counting_generator as *const () as u64, 0, RuntimeValue::NIL);

    // Each next() should increment the counter
    let val0 = rt_generator_next(gen);
    assert_eq!(val0.as_int(), 0);

    let val1 = rt_generator_next(gen);
    assert_eq!(val1.as_int(), 1);

    let val2 = rt_generator_next(gen);
    assert_eq!(val2.as_int(), 2);

    // Counter should have been incremented 3 times
    assert_eq!(GENERATOR_COUNTER.load(Ordering::SeqCst), 3);
}
