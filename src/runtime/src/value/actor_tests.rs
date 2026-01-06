//! Tests for actor functionality

use super::{rt_actor_spawn, rt_actor_send, rt_actor_recv, rt_actor_join,
            rt_actor_id, rt_actor_is_alive};
use crate::value::RuntimeValue;
use std::sync::atomic::{AtomicI32, AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

// Test helper: Counter for tracking actor executions
static ACTOR_COUNTER: AtomicI32 = AtomicI32::new(0);

// Test helper: Simple actor that increments counter
extern "C" fn counting_actor(_ctx: *const u8) {
    ACTOR_COUNTER.fetch_add(1, Ordering::SeqCst);
}

// Test helper: Actor that receives and processes a message
extern "C" fn echo_actor(_ctx: *const u8) {
    // Receive a message
    let msg = rt_actor_recv();

    // Echo it back by incrementing counter with the value
    if msg.is_int() {
        ACTOR_COUNTER.fetch_add(msg.as_int() as i32, Ordering::SeqCst);
    }
}

// Test helper: Actor that receives multiple messages
extern "C" fn multi_recv_actor(_ctx: *const u8) {
    for _ in 0..3 {
        let msg = rt_actor_recv();
        if msg.is_int() {
            ACTOR_COUNTER.fetch_add(msg.as_int() as i32, Ordering::SeqCst);
        }
    }
}

// Test helper: Actor that stores execution flag
static ACTOR_RAN: AtomicBool = AtomicBool::new(false);

extern "C" fn flag_setting_actor(_ctx: *const u8) {
    ACTOR_RAN.store(true, Ordering::SeqCst);
    // Sleep briefly to ensure async execution
    thread::sleep(Duration::from_millis(10));
}

#[test]
fn test_actor_spawn() {
    ACTOR_COUNTER.store(0, Ordering::SeqCst);

    let actor = rt_actor_spawn(
        counting_actor as u64,
        RuntimeValue::NIL
    );

    // Should return a valid actor handle
    assert!(actor.is_heap());

    // Give actor time to execute
    thread::sleep(Duration::from_millis(50));

    // Actor should have incremented counter
    assert_eq!(ACTOR_COUNTER.load(Ordering::SeqCst), 1);
}

#[test]
fn test_actor_spawn_null_body() {
    // Spawn actor with null body function (should create mailbox but do nothing)
    let actor = rt_actor_spawn(0, RuntimeValue::NIL);

    // Should still return a valid handle
    assert!(actor.is_heap());

    // Should have valid ID
    let id = rt_actor_id(actor);
    assert!(id > 0);
}

#[test]
fn test_actor_id() {
    let actor1 = rt_actor_spawn(counting_actor as u64, RuntimeValue::NIL);
    let actor2 = rt_actor_spawn(counting_actor as u64, RuntimeValue::NIL);

    let id1 = rt_actor_id(actor1);
    let id2 = rt_actor_id(actor2);

    // Both should have valid IDs
    assert!(id1 > 0);
    assert!(id2 > 0);

    // IDs should be different
    assert_ne!(id1, id2);
}

#[test]
fn test_actor_id_invalid_value() {
    // Try to get ID from non-actor value
    let not_an_actor = RuntimeValue::from_int(42);
    let id = rt_actor_id(not_an_actor);

    // Should return 0 for invalid actor
    assert_eq!(id, 0);
}

#[test]
fn test_actor_send_and_recv() {
    ACTOR_COUNTER.store(0, Ordering::SeqCst);

    // Spawn echo actor
    let actor = rt_actor_spawn(echo_actor as u64, RuntimeValue::NIL);

    // Give actor time to start
    thread::sleep(Duration::from_millis(20));

    // Send a message
    let message = RuntimeValue::from_int(42);
    rt_actor_send(actor, message);

    // Give actor time to process
    thread::sleep(Duration::from_millis(50));

    // Counter should be incremented by the message value
    assert_eq!(ACTOR_COUNTER.load(Ordering::SeqCst), 42);
}

#[test]
fn test_actor_send_invalid_actor() {
    // Try to send to non-actor value (should not crash)
    let not_an_actor = RuntimeValue::from_int(99);
    let message = RuntimeValue::from_int(123);

    rt_actor_send(not_an_actor, message);
    // Should complete without panic
}

#[test]
fn test_actor_multiple_messages() {
    ACTOR_COUNTER.store(0, Ordering::SeqCst);

    // Spawn actor that receives 3 messages
    let actor = rt_actor_spawn(multi_recv_actor as u64, RuntimeValue::NIL);

    // Give actor time to start
    thread::sleep(Duration::from_millis(20));

    // Send multiple messages
    rt_actor_send(actor, RuntimeValue::from_int(10));
    rt_actor_send(actor, RuntimeValue::from_int(20));
    rt_actor_send(actor, RuntimeValue::from_int(30));

    // Give actor time to process all messages
    thread::sleep(Duration::from_millis(100));

    // Counter should be sum of all messages: 10 + 20 + 30 = 60
    assert_eq!(ACTOR_COUNTER.load(Ordering::SeqCst), 60);
}

#[test]
fn test_actor_join() {
    ACTOR_RAN.store(false, Ordering::SeqCst);

    let actor = rt_actor_spawn(flag_setting_actor as u64, RuntimeValue::NIL);

    // Join should wait for actor to complete
    let result = rt_actor_join(actor);

    // Should return 1 for success
    assert_eq!(result, 1);

    // Actor should have run
    assert!(ACTOR_RAN.load(Ordering::SeqCst));
}

#[test]
fn test_actor_join_invalid_actor() {
    // Try to join non-actor value
    let not_an_actor = RuntimeValue::from_int(42);
    let result = rt_actor_join(not_an_actor);

    // Should return 0 for failure
    assert_eq!(result, 0);
}

#[test]
fn test_actor_is_alive() {
    // Spawn a long-running actor
    extern "C" fn long_running_actor(_ctx: *const u8) {
        thread::sleep(Duration::from_millis(200));
    }

    let actor = rt_actor_spawn(long_running_actor as u64, RuntimeValue::NIL);

    // Should be alive immediately after spawn
    let alive = rt_actor_is_alive(actor);
    assert_eq!(alive, 1);

    // Clean up
    rt_actor_join(actor);
}

#[test]
fn test_actor_is_alive_invalid() {
    // Try to check if non-actor is alive
    let not_an_actor = RuntimeValue::from_int(42);
    let alive = rt_actor_is_alive(not_an_actor);

    // Should return 0 for invalid actor
    assert_eq!(alive, 0);
}

#[test]
fn test_actor_concurrent_spawns() {
    ACTOR_COUNTER.store(0, Ordering::SeqCst);

    // Spawn multiple actors concurrently
    let actor1 = rt_actor_spawn(counting_actor as u64, RuntimeValue::NIL);
    let actor2 = rt_actor_spawn(counting_actor as u64, RuntimeValue::NIL);
    let actor3 = rt_actor_spawn(counting_actor as u64, RuntimeValue::NIL);

    // All should have valid, unique IDs
    let id1 = rt_actor_id(actor1);
    let id2 = rt_actor_id(actor2);
    let id3 = rt_actor_id(actor3);

    assert!(id1 > 0);
    assert!(id2 > 0);
    assert!(id3 > 0);
    assert_ne!(id1, id2);
    assert_ne!(id2, id3);
    assert_ne!(id1, id3);

    // Wait for all to complete
    thread::sleep(Duration::from_millis(100));

    // All three should have incremented the counter
    assert_eq!(ACTOR_COUNTER.load(Ordering::SeqCst), 3);
}

#[test]
fn test_actor_message_ordering() {
    ACTOR_COUNTER.store(0, Ordering::SeqCst);

    // Actor that processes messages in order
    extern "C" fn ordered_actor(_ctx: *const u8) {
        let mut sum = 0i32;
        for _ in 0..3 {
            let msg = rt_actor_recv();
            if msg.is_int() {
                sum += msg.as_int() as i32;
            }
        }
        ACTOR_COUNTER.store(sum, Ordering::SeqCst);
    }

    let actor = rt_actor_spawn(ordered_actor as u64, RuntimeValue::NIL);
    thread::sleep(Duration::from_millis(20));

    // Send messages in order
    rt_actor_send(actor, RuntimeValue::from_int(1));
    rt_actor_send(actor, RuntimeValue::from_int(2));
    rt_actor_send(actor, RuntimeValue::from_int(3));

    thread::sleep(Duration::from_millis(100));

    // Sum should be 1 + 2 + 3 = 6
    assert_eq!(ACTOR_COUNTER.load(Ordering::SeqCst), 6);
}

#[test]
fn test_actor_recv_timeout() {
    // Actor that tries to receive when no message is available
    static RECV_FAILED: AtomicBool = AtomicBool::new(false);

    extern "C" fn timeout_actor(_ctx: *const u8) {
        let msg = rt_actor_recv();
        if msg.is_nil() {
            // Receive timed out as expected
            RECV_FAILED.store(true, Ordering::SeqCst);
        }
    }

    RECV_FAILED.store(false, Ordering::SeqCst);

    let actor = rt_actor_spawn(timeout_actor as u64, RuntimeValue::NIL);

    // Don't send any message - let recv timeout
    thread::sleep(Duration::from_millis(100));

    // Join to ensure actor completed
    rt_actor_join(actor);

    // Recv should have timed out
    assert!(RECV_FAILED.load(Ordering::SeqCst));
}

#[test]
fn test_actor_with_context() {
    // Test spawning actor with context value
    static CONTEXT_VALUE: AtomicI32 = AtomicI32::new(0);

    extern "C" fn context_actor(ctx: *const u8) {
        // In a real implementation, context would be properly passed
        // For now, just verify actor executes
        CONTEXT_VALUE.store(123, Ordering::SeqCst);
    }

    CONTEXT_VALUE.store(0, Ordering::SeqCst);

    // Create context value (heap-allocated)
    use crate::value::rt_array_new;
    let ctx = rt_array_new(1);

    let actor = rt_actor_spawn(context_actor as u64, ctx);

    thread::sleep(Duration::from_millis(50));

    // Actor should have executed
    assert_eq!(CONTEXT_VALUE.load(Ordering::SeqCst), 123);

    rt_actor_join(actor);
}
