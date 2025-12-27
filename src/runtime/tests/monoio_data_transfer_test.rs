// Data transfer test for monoio - tests actual read/write operations
#![cfg(feature = "monoio-net")]

use simple_runtime::value::RuntimeValue;
use simple_runtime::{
    monoio_tcp_listen, monoio_tcp_accept, monoio_tcp_connect,
    monoio_tcp_read, monoio_tcp_write, monoio_tcp_close,
    monoio_udp_bind, monoio_udp_send_to, monoio_udp_recv_from, monoio_udp_close
};
use simple_runtime::value::{rt_string_new, rt_array_new};
use std::thread;
use std::time::Duration;

fn create_string(s: &str) -> RuntimeValue {
    unsafe { rt_string_new(s.as_ptr(), s.len() as u64) }
}

fn create_buffer(size: usize) -> RuntimeValue {
    rt_array_new(size as u64)
}

fn buffer_to_vec(buffer: RuntimeValue, len: usize) -> Vec<u8> {
    let mut result = Vec::new();
    if buffer.is_heap() {
        let ptr = buffer.as_heap_ptr();
        unsafe {
            let arr_ptr = ptr as *const simple_runtime::value::RuntimeArray;
            let slice = (*arr_ptr).as_slice();
            for i in 0..len.min((*arr_ptr).len as usize) {
                result.push(slice[i].as_int() as u8);
            }
        }
    }
    result
}

fn vec_to_buffer(data: &[u8]) -> RuntimeValue {
    let buffer = create_buffer(data.len());
    if buffer.is_heap() {
        let ptr = buffer.as_heap_ptr();
        unsafe {
            let arr_ptr = ptr as *mut simple_runtime::value::RuntimeArray;
            let slice = (*arr_ptr).as_mut_slice();
            for (i, &byte) in data.iter().enumerate() {
                slice[i] = RuntimeValue::from_int(byte as i64);
            }
            (*arr_ptr).len = data.len() as u64;
        }
    }
    buffer
}

#[test]
fn test_tcp_echo() {
    // Start a TCP server in a background thread
    let server_thread = thread::spawn(|| {
        let addr = create_string("127.0.0.1:9876");
        let listener = monoio_tcp_listen(addr);
        assert!(listener.as_int() > 0, "Failed to create listener");

        println!("Server: Listening on 127.0.0.1:9876");

        // Accept connection
        let stream = monoio_tcp_accept(listener);
        assert!(stream.as_int() > 0, "Failed to accept connection");

        println!("Server: Accepted connection");

        // Read data
        let read_buffer = create_buffer(1024);
        let bytes_read = monoio_tcp_read(stream, read_buffer, 1024);
        println!("Server: Read {} bytes", bytes_read.as_int());

        if bytes_read.as_int() > 0 {
            // Echo back
            let bytes_written = monoio_tcp_write(stream, read_buffer, bytes_read.as_int());
            println!("Server: Wrote {} bytes", bytes_written.as_int());
            assert_eq!(bytes_written.as_int(), bytes_read.as_int(), "Write failed");
        }

        // Close
        monoio_tcp_close(stream);
        println!("Server: Closed connection");
    });

    // Give server time to start
    thread::sleep(Duration::from_millis(100));

    // Connect as client
    let addr = create_string("127.0.0.1:9876");
    let client = monoio_tcp_connect(addr);
    assert!(client.as_int() > 0, "Failed to connect");

    println!("Client: Connected");

    // Send data
    let message = b"Hello, TCP!";
    let write_buffer = vec_to_buffer(message);
    let bytes_sent = monoio_tcp_write(client, write_buffer, message.len() as i64);
    println!("Client: Sent {} bytes", bytes_sent.as_int());
    assert_eq!(bytes_sent.as_int(), message.len() as i64, "Send failed");

    // Receive echo
    let read_buffer = create_buffer(1024);
    let bytes_received = monoio_tcp_read(client, read_buffer, 1024);
    println!("Client: Received {} bytes", bytes_received.as_int());
    assert_eq!(bytes_received.as_int(), message.len() as i64, "Receive failed");

    // Verify data
    let received_data = buffer_to_vec(read_buffer, bytes_received.as_int() as usize);
    assert_eq!(&received_data[..], message, "Data mismatch!");

    println!("Client: Data verified: {:?}", String::from_utf8_lossy(&received_data));

    // Close
    monoio_tcp_close(client);

    // Wait for server
    server_thread.join().unwrap();

    println!("✅ TCP echo test passed!");
}

#[test]
fn test_udp_datagram() {
    // Create receiver
    let receiver_addr = create_string("127.0.0.1:9877");
    let receiver = monoio_udp_bind(receiver_addr);
    assert!(receiver.as_int() > 0, "Failed to bind receiver");

    println!("Receiver: Bound to 127.0.0.1:9877");

    // Create sender
    let sender_addr = create_string("127.0.0.1:0"); // Any port
    let sender = monoio_udp_bind(sender_addr);
    assert!(sender.as_int() > 0, "Failed to bind sender");

    println!("Sender: Bound");

    // Send data in background thread
    let sender_thread = thread::spawn(move || {
        thread::sleep(Duration::from_millis(50)); // Let receiver start

        let message = b"Hello, UDP!";
        let buffer = vec_to_buffer(message);
        let target_addr = create_string("127.0.0.1:9877");

        let bytes_sent = monoio_udp_send_to(sender, buffer, message.len() as i64, target_addr);
        println!("Sender: Sent {} bytes", bytes_sent.as_int());
        assert_eq!(bytes_sent.as_int(), message.len() as i64, "Send failed");

        monoio_udp_close(sender);
    });

    // Receive data
    let recv_buffer = create_buffer(1024);
    let bytes_received = monoio_udp_recv_from(receiver, recv_buffer, 1024);
    println!("Receiver: Received {} bytes", bytes_received.as_int());

    let message = b"Hello, UDP!";
    assert_eq!(bytes_received.as_int(), message.len() as i64, "Receive size mismatch");

    // Verify data
    let received_data = buffer_to_vec(recv_buffer, bytes_received.as_int() as usize);
    assert_eq!(&received_data[..], message, "Data mismatch!");

    println!("Receiver: Data verified: {:?}", String::from_utf8_lossy(&received_data));

    // Close
    monoio_udp_close(receiver);

    // Wait for sender
    sender_thread.join().unwrap();

    println!("✅ UDP datagram test passed!");
}

#[test]
fn test_buffer_conversion() {
    // Test buffer_to_vec and vec_to_buffer
    let data = b"Test data 123!";

    // Convert to buffer
    let buffer = vec_to_buffer(data);
    assert!(buffer.is_heap(), "Buffer should be heap-allocated");

    // Convert back to vec
    let recovered = buffer_to_vec(buffer, data.len());
    assert_eq!(&recovered[..], data, "Round-trip conversion failed");

    println!("✅ Buffer conversion test passed!");
}
