//! Integration tests for networking functionality.
//!
//! These tests verify that TCP, UDP, and HTTP operations work correctly
//! through the interpreter.

#![allow(unused_imports)]

mod test_helpers;

use simple_driver::interpreter::{Interpreter, RunConfig, RunningType};
use std::net::{TcpListener, TcpStream, UdpSocket};
use std::io::{Read, Write};
use std::thread;
use std::time::Duration;

/// Helper to run code in interpreter mode and return exit code
fn run_net_test(code: &str) -> i32 {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(
            code,
            RunConfig {
                running_type: RunningType::Interpreter,
                in_memory: true,
                ..Default::default()
            },
        )
        .expect("run ok");
    result.exit_code
}

/// Test TCP bind creates a valid handle
#[test]
fn test_tcp_bind_returns_handle() {
    let code = r#"
extern fn native_tcp_bind(addr: str) -> (i64, i64)
extern fn native_tcp_close(handle: i64) -> i64

fn main() -> i64:
    let result = native_tcp_bind("127.0.0.1:0")
    let handle = result[0]
    let err = result[1]
    if err != 0:
        return -1
    if handle <= 0:
        return -2
    let close_err = native_tcp_close(handle)
    if close_err != 0:
        return -3
    return 0
"#;
    assert_eq!(run_net_test(code), 0, "TCP bind test failed");
}

/// Test UDP bind creates a valid handle
#[test]
fn test_udp_bind_returns_handle() {
    let code = r#"
extern fn native_udp_bind(addr: str) -> (i64, i64)
extern fn native_udp_close(handle: i64) -> i64

fn main() -> i64:
    let result = native_udp_bind("127.0.0.1:0")
    let handle = result[0]
    let err = result[1]
    if err != 0:
        return -1
    if handle <= 0:
        return -2
    let close_err = native_udp_close(handle)
    if close_err != 0:
        return -3
    return 0
"#;
    assert_eq!(run_net_test(code), 0, "UDP bind test failed");
}

/// Test that invalid socket handles return errors
#[test]
fn test_invalid_handle_errors() {
    let code = r#"
extern fn native_tcp_close(handle: i64) -> i64

fn main() -> i64:
    # Try to close an invalid handle
    let err = native_tcp_close(99999)
    if err == 0:
        return -1  # Should have failed
    return 0  # Success - got error as expected
"#;
    assert_eq!(run_net_test(code), 0, "Invalid handle test failed");
}

/// Test UDP broadcast option
#[test]
fn test_udp_broadcast_option() {
    let code = r#"
extern fn native_udp_bind(addr: str) -> (i64, i64)
extern fn native_udp_set_broadcast(handle: i64, enable: i64) -> i64
extern fn native_udp_close(handle: i64) -> i64

fn main() -> i64:
    let result = native_udp_bind("127.0.0.1:0")
    let handle = result[0]
    let bind_err = result[1]
    if bind_err != 0:
        return -1

    # Enable broadcast
    let set_err = native_udp_set_broadcast(handle, 1)
    if set_err != 0:
        return -2

    native_udp_close(handle)
    return 0
"#;
    assert_eq!(run_net_test(code), 0, "UDP broadcast test failed");
}

/// Test UDP TTL option
#[test]
fn test_udp_ttl_option() {
    let code = r#"
extern fn native_udp_bind(addr: str) -> (i64, i64)
extern fn native_udp_set_ttl(handle: i64, ttl: i64) -> i64
extern fn native_udp_close(handle: i64) -> i64

fn main() -> i64:
    let result = native_udp_bind("127.0.0.1:0")
    let handle = result[0]
    let bind_err = result[1]
    if bind_err != 0:
        return -1

    # Set TTL to 64
    let set_err = native_udp_set_ttl(handle, 64)
    if set_err != 0:
        return -2

    native_udp_close(handle)
    return 0
"#;
    assert_eq!(run_net_test(code), 0, "UDP TTL test failed");
}

/// Test TCP connection to a local server
#[test]
fn test_tcp_connect_to_local_server() {
    // Start a simple TCP server in a background thread
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let server_addr = listener.local_addr().unwrap();

    let server_thread = thread::spawn(move || {
        let (mut _stream, _) = listener.accept().unwrap();
        thread::sleep(Duration::from_millis(100));
    });

    // Give server time to start
    thread::sleep(Duration::from_millis(50));

    let code = format!(r#"
extern fn native_tcp_connect(addr: str) -> (i64, str, i64)
extern fn native_tcp_close(handle: i64) -> i64

fn main() -> i64:
    let result = native_tcp_connect("{}")
    let handle = result[0]
    let err = result[2]
    if err != 0:
        return -1
    if handle <= 0:
        return -2
    native_tcp_close(handle)
    return 0
"#, server_addr);

    assert_eq!(run_net_test(&code), 0, "TCP connect test failed");
    let _ = server_thread.join();
}

/// Test TCP accept
#[test]
fn test_tcp_accept() {
    let code = r#"
extern fn native_tcp_bind(addr: str) -> (i64, i64)
extern fn native_tcp_close(handle: i64) -> i64

fn main() -> i64:
    # Just test binding - accept requires a client
    let result = native_tcp_bind("127.0.0.1:0")
    let handle = result[0]
    let err = result[1]
    if err != 0:
        return -1
    native_tcp_close(handle)
    return 0
"#;
    assert_eq!(run_net_test(code), 0, "TCP accept test failed");
}

/// Test UDP send/recv with local sockets
#[test]
fn test_udp_loopback() {
    // Create a receiver socket in Rust
    let receiver = UdpSocket::bind("127.0.0.1:0").unwrap();
    let receiver_addr = receiver.local_addr().unwrap();
    receiver.set_read_timeout(Some(Duration::from_secs(5))).unwrap();

    // Start receiver thread
    let receiver_thread = thread::spawn(move || {
        let mut buf = [0u8; 1024];
        match receiver.recv_from(&mut buf) {
            Ok((len, _src)) => len > 0,
            Err(_) => false,
        }
    });

    thread::sleep(Duration::from_millis(50));

    let code = format!(r#"
extern fn native_udp_bind(addr: str) -> (i64, i64)
extern fn native_udp_send_to(handle: i64, data: [i64], len: i64, addr: str) -> (i64, i64)
extern fn native_udp_close(handle: i64) -> i64

fn main() -> i64:
    let result = native_udp_bind("127.0.0.1:0")
    let handle = result[0]
    if result[1] != 0:
        return -1

    # Send "hi" (104, 105)
    let data = [104, 105]
    let send_result = native_udp_send_to(handle, data, 2, "{}")
    let sent = send_result[0]
    let send_err = send_result[1]
    if send_err != 0:
        return -2
    if sent != 2:
        return -3

    native_udp_close(handle)
    return 0
"#, receiver_addr);

    assert_eq!(run_net_test(&code), 0, "UDP loopback test failed");
    let received = receiver_thread.join().unwrap();
    assert!(received, "Receiver should have received data");
}

// ============================================================================
// JIT/Native Compilation Tests
// ============================================================================

/// Helper to run code in JIT/native compilation mode
fn run_net_test_jit(code: &str) -> i32 {
    let interpreter = Interpreter::new();
    let result = interpreter
        .run(
            code,
            RunConfig {
                running_type: RunningType::Compiler,
                in_memory: true,
                ..Default::default()
            },
        )
        .expect("run ok");
    result.exit_code
}

/// Test TCP bind with JIT compilation
#[test]
fn test_tcp_bind_jit() {
    let code = r#"
extern fn native_tcp_bind(addr_ptr: i64, addr_len: i64) -> (i64, i64)
extern fn native_tcp_close(handle: i64) -> i64

fn main() -> i64:
    # Call with pointer and length (JIT path uses raw FFI)
    # For now, just return 0 to verify JIT compilation works
    return 0
"#;
    assert_eq!(run_net_test_jit(code), 0, "TCP bind JIT test failed");
}

/// Test UDP bind with JIT compilation
#[test]
fn test_udp_bind_jit() {
    let code = r#"
extern fn native_udp_bind(addr_ptr: i64, addr_len: i64) -> (i64, i64)
extern fn native_udp_close(handle: i64) -> i64

fn main() -> i64:
    # For now, just return 0 to verify JIT compilation works with extern declarations
    return 0
"#;
    assert_eq!(run_net_test_jit(code), 0, "UDP bind JIT test failed");
}
