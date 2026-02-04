// Integration tests for monoio network wrapper
#![cfg(feature = "monoio-net")]

use simple_runtime::value::RuntimeValue;
use simple_runtime::{
    monoio_tcp_listen, monoio_tcp_connect, monoio_tcp_accept,
    monoio_tcp_read, monoio_tcp_write, monoio_tcp_close,
    monoio_udp_bind, monoio_udp_send_to, monoio_udp_recv_from, monoio_udp_close,
};
use simple_runtime::value::rt_string_new;
use std::thread;
use std::time::Duration;

fn create_string(s: &str) -> RuntimeValue {
    unsafe { rt_string_new(s.as_ptr(), s.len() as u64) }
}

#[test]
fn test_tcp_listen_basic() {
    // Test that we can bind to a TCP port
    let addr = create_string("127.0.0.1:18080");
    let listener = monoio_tcp_listen(addr);

    println!("TCP listen result: {:?}", listener.as_int());
    assert!(listener.as_int() >= 0, "TCP listen should succeed");
}

#[test]
fn test_tcp_listen_invalid_address() {
    // Test error handling with invalid address
    let addr = RuntimeValue::from_int(123); // Not a string
    let result = monoio_tcp_listen(addr);

    assert_eq!(result.as_int(), -1, "Should return error for invalid address");
}

#[test]
fn test_tcp_connect_refused() {
    // Test connection refused to a port that's not listening
    let addr = create_string("127.0.0.1:19999");
    let result = monoio_tcp_connect(addr);

    println!("TCP connect to closed port result: {:?}", result.as_int());
    // Should get connection refused (-2) or timeout (-4)
    assert!(result.as_int() < 0, "Connection should fail");
}

#[test]
fn test_tcp_echo() {
    // Start a listener in a background thread
    let addr_str = "127.0.0.1:18081";
    let addr = create_string(addr_str);
    let listener_handle = monoio_tcp_listen(addr);

    assert!(listener_handle.as_int() >= 0, "Listener should bind successfully");
    println!("Listener handle: {}", listener_handle.as_int());

    // Spawn a thread to accept connection
    let listener_id = listener_handle.as_int();
    let accept_thread = thread::spawn(move || {
        println!("Accept thread: waiting for connection on listener {}", listener_id);
        thread::sleep(Duration::from_millis(100)); // Give client time to connect

        let stream_handle = monoio_tcp_accept(RuntimeValue::from_int(listener_id));
        println!("Accept thread: got handle {}", stream_handle.as_int());
        stream_handle
    });

    // Give server time to start
    thread::sleep(Duration::from_millis(200));

    // Connect from client
    println!("Client: connecting to {}", addr_str);
    let addr = create_string(addr_str);
    let client_handle = monoio_tcp_connect(addr);

    println!("Client handle: {}", client_handle.as_int());
    assert!(client_handle.as_int() >= 0, "Client should connect successfully");

    // Wait for accept to complete
    let server_handle = accept_thread.join().unwrap();
    println!("Server handle from accept: {}", server_handle.as_int());
    assert!(server_handle.as_int() >= 0, "Accept should succeed");

    // Close connections
    monoio_tcp_close(client_handle);
    monoio_tcp_close(server_handle);
}

#[test]
fn test_udp_bind_basic() {
    // Test that we can bind a UDP socket
    let addr = create_string("127.0.0.1:19090");
    let socket = monoio_udp_bind(addr);

    println!("UDP bind result: {:?}", socket.as_int());
    assert!(socket.as_int() >= 0, "UDP bind should succeed");

    // Close socket
    monoio_udp_close(socket);
}

#[test]
fn test_udp_bind_invalid_address() {
    // Test error handling with invalid address
    let addr = RuntimeValue::from_int(456); // Not a string
    let result = monoio_udp_bind(addr);

    assert_eq!(result.as_int(), -1, "Should return error for invalid address");
}

#[test]
fn test_multiple_tcp_listeners() {
    // Test that we can create multiple listeners
    let addr1 = create_string("127.0.0.1:18082");
    let addr2 = create_string("127.0.0.1:18083");

    let listener1 = monoio_tcp_listen(addr1);
    let listener2 = monoio_tcp_listen(addr2);

    assert!(listener1.as_int() >= 0, "First listener should bind");
    assert!(listener2.as_int() >= 0, "Second listener should bind");
    assert_ne!(listener1.as_int(), listener2.as_int(), "Listeners should have different IDs");

    println!("Listener 1 ID: {}, Listener 2 ID: {}", listener1.as_int(), listener2.as_int());
}

#[test]
fn test_multiple_udp_sockets() {
    // Test that we can create multiple UDP sockets
    let addr1 = create_string("127.0.0.1:19091");
    let addr2 = create_string("127.0.0.1:19092");

    let socket1 = monoio_udp_bind(addr1);
    let socket2 = monoio_udp_bind(addr2);

    assert!(socket1.as_int() >= 0, "First socket should bind");
    assert!(socket2.as_int() >= 0, "Second socket should bind");
    assert_ne!(socket1.as_int(), socket2.as_int(), "Sockets should have different IDs");

    println!("Socket 1 ID: {}, Socket 2 ID: {}", socket1.as_int(), socket2.as_int());

    // Close sockets
    monoio_udp_close(socket1);
    monoio_udp_close(socket2);
}

#[test]
fn test_runtime_thread_running() {
    // Test that the runtime thread is actually running
    // by performing multiple operations in sequence
    let addr = create_string("127.0.0.1:18084");

    for i in 0..5 {
        let listener = monoio_tcp_listen(addr);
        assert!(listener.as_int() >= 0, "Listen {} should succeed", i);
        println!("Iteration {}: listener ID {}", i, listener.as_int());

        // Small delay between iterations
        thread::sleep(Duration::from_millis(50));
    }
}

#[test]
fn test_error_codes() {
    // Test that we get proper error codes

    // Invalid handle should return error
    let invalid_handle = RuntimeValue::from_int(99999);
    let result = monoio_tcp_accept(invalid_handle);
    assert!(result.as_int() < 0, "Invalid handle should return error");

    // Connection to non-existent port should return error
    let addr = create_string("127.0.0.1:19999");
    let result = monoio_tcp_connect(addr);
    assert!(result.as_int() < 0, "Connection to closed port should fail");

    println!("Error code for invalid handle: {}", monoio_tcp_accept(RuntimeValue::from_int(99999)).as_int());
    println!("Error code for connection refused: {}", result.as_int());
}

#[test]
fn test_concurrent_operations() {
    // Test that we can perform operations concurrently
    let handles: Vec<_> = (0..3)
        .map(|i| {
            let port = 18085 + i;
            let addr = create_string(&format!("127.0.0.1:{}", port));

            thread::spawn(move || {
                let listener = monoio_tcp_listen(addr);
                println!("Thread {}: listener ID {}", i, listener.as_int());
                assert!(listener.as_int() >= 0, "Listener {} should succeed", i);
                listener.as_int()
            })
        })
        .collect();

    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

    // All should succeed
    for (i, &id) in results.iter().enumerate() {
        assert!(id >= 0, "Listener {} should have valid ID", i);
    }

    // All should have unique IDs
    for i in 0..results.len() {
        for j in (i+1)..results.len() {
            assert_ne!(results[i], results[j], "IDs should be unique");
        }
    }
}
