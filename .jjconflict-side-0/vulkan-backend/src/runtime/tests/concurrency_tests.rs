use simple_runtime::concurrency::{join_actor, send_to, spawn_actor, Message};
use std::time::Duration;

#[test]
fn actor_spawn_and_join() {
    let handle = spawn_actor(|inbox, outbox| {
        if let Ok(msg) = inbox.recv() {
            outbox.send(msg).unwrap();
        }
    });

    handle.send(Message::Value("hello".to_string())).unwrap();
    let reply = handle.recv().unwrap();
    assert!(matches!(reply, Message::Value(s) if s == "hello"));
    handle.join().unwrap();
}

#[test]
fn actor_id_is_unique() {
    let h1 = spawn_actor(|_, _| {});
    let h2 = spawn_actor(|_, _| {});

    assert_ne!(h1.id(), h2.id());

    h1.join().unwrap();
    h2.join().unwrap();
}

#[test]
fn actor_handles_compare_equal_by_id() {
    let h1 = spawn_actor(|_, _| {});
    let h1_clone = h1.clone();

    assert_eq!(h1, h1_clone);
    assert_eq!(h1.id(), h1_clone.id());

    h1.join().unwrap();
}

#[test]
fn actor_send_bytes_message() {
    let handle = spawn_actor(|inbox, outbox| {
        if let Ok(Message::Bytes(data)) = inbox.recv() {
            outbox.send(Message::Bytes(data)).unwrap();
        }
    });

    handle.send(Message::Bytes(vec![1, 2, 3, 4])).unwrap();
    let reply = handle.recv().unwrap();
    assert!(matches!(reply, Message::Bytes(v) if v == vec![1, 2, 3, 4]));
    handle.join().unwrap();
}

#[test]
fn actor_recv_timeout_returns_error_on_timeout() {
    let handle = spawn_actor(|_inbox, _outbox| {
        // Actor does nothing, causing timeout on recv
        std::thread::sleep(Duration::from_millis(100));
    });

    let result = handle.recv_timeout(Duration::from_millis(10));
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("timeout"));
    handle.join().unwrap();
}

#[test]
fn actor_try_recv_returns_none_when_empty() {
    let handle = spawn_actor(|_inbox, _outbox| {
        std::thread::sleep(Duration::from_millis(50));
    });

    // No message has been sent by actor yet
    let result = handle.try_recv().unwrap();
    assert!(result.is_none());
    handle.join().unwrap();
}

#[test]
fn actor_try_recv_returns_message_when_available() {
    let handle = spawn_actor(|_inbox, outbox| {
        outbox.send(Message::Value("ready".to_string())).unwrap();
    });

    // Wait briefly for actor to send
    std::thread::sleep(Duration::from_millis(20));

    let result = handle.try_recv().unwrap();
    assert!(result.is_some());
    assert!(matches!(result.unwrap(), Message::Value(s) if s == "ready"));
    handle.join().unwrap();
}

#[test]
fn scheduler_send_to_works() {
    let handle = spawn_actor(|inbox, outbox| {
        if let Ok(msg) = inbox.recv() {
            outbox.send(msg).unwrap();
        }
    });

    let id = handle.id();
    send_to(id, Message::Value("via scheduler".to_string())).unwrap();

    let reply = handle.recv().unwrap();
    assert!(matches!(reply, Message::Value(s) if s == "via scheduler"));
    handle.join().unwrap();
}

#[test]
fn scheduler_send_to_unknown_actor_fails() {
    let result = send_to(999999, Message::Value("test".to_string()));
    assert!(result.is_err());
    assert!(result.unwrap_err().contains("unknown actor"));
}

#[test]
fn scheduler_join_actor_works() {
    let handle = spawn_actor(|_inbox, _outbox| {
        // Quick actor
    });

    let id = handle.id();
    join_actor(id).unwrap();
    // join_actor returns Ok even if already joined
    join_actor(id).unwrap();
}

#[test]
fn actor_join_can_be_called_multiple_times() {
    let handle = spawn_actor(|_inbox, _outbox| {});

    handle.join().unwrap();
    // Second join should also succeed (no-op)
    handle.join().unwrap();
}

#[test]
fn actor_echo_multiple_messages() {
    let handle = spawn_actor(|inbox, outbox| {
        for _ in 0..3 {
            if let Ok(msg) = inbox.recv() {
                outbox.send(msg).unwrap();
            }
        }
    });

    for i in 0..3 {
        handle.send(Message::Value(format!("msg{}", i))).unwrap();
        let reply = handle.recv().unwrap();
        assert!(matches!(reply, Message::Value(s) if s == format!("msg{}", i)));
    }
    handle.join().unwrap();
}

#[test]
fn message_debug_format() {
    let val_msg = Message::Value("test".to_string());
    let bytes_msg = Message::Bytes(vec![1, 2, 3]);

    // Just verify Debug works without panic
    let _ = format!("{:?}", val_msg);
    let _ = format!("{:?}", bytes_msg);
}

#[test]
fn message_clone() {
    let original = Message::Value("original".to_string());
    let cloned = original.clone();

    assert!(matches!(cloned, Message::Value(s) if s == "original"));

    let bytes_original = Message::Bytes(vec![10, 20, 30]);
    let bytes_cloned = bytes_original.clone();

    assert!(matches!(bytes_cloned, Message::Bytes(v) if v == vec![10, 20, 30]));
}

#[test]
fn actor_handle_debug_format() {
    let handle = spawn_actor(|_inbox, _outbox| {});

    // Verify Debug works
    let debug_str = format!("{:?}", handle);
    assert!(debug_str.contains("ActorHandle"));

    handle.join().unwrap();
}
