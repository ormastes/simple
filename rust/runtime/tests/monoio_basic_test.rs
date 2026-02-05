// Basic monoio API test - just verify functions can be called
#![cfg(feature = "monoio-net")]

use simple_runtime::value::RuntimeValue;
use simple_runtime::{monoio_tcp_listen, monoio_udp_bind};
use simple_runtime::value::rt_string_new;

fn create_string(s: &str) -> RuntimeValue {
    unsafe { rt_string_new(s.as_ptr(), s.len() as u64) }
}

#[test]
fn test_api_exists() {
    // Just verify the functions exist and can be called
    // This tests compilation and linking
    let addr = create_string("127.0.0.1:0"); // Port 0 = any free port
    println!("Testing TCP listen API...");
    let result = monoio_tcp_listen(addr);
    println!("TCP listen result: {}", result.as_int());

    let addr2 = create_string("127.0.0.1:0");
    println!("Testing UDP bind API...");
    let result2 = monoio_udp_bind(addr2);
    println!("UDP bind result: {}", result2.as_int());

    // We don't care about the actual result, just that the calls work
    println!("API test complete - functions callable");
}

#[test]
fn test_error_handling() {
    // Test that invalid input returns error
    let invalid = RuntimeValue::from_int(999);
    let result = monoio_tcp_listen(invalid);
    assert_eq!(result.as_int(), -1, "Invalid input should return -1");
}
