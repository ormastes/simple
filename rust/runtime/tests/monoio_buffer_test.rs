// Buffer management test for monoio
#![cfg(feature = "monoio-net")]

use simple_runtime::value::RuntimeValue;
use simple_runtime::value::{rt_array_new, RuntimeArray};

fn create_buffer(size: usize) -> RuntimeValue {
    rt_array_new(size as u64)
}

fn fill_buffer(buffer: RuntimeValue, data: &[u8]) {
    if buffer.is_heap() {
        let ptr = buffer.as_heap_ptr();
        unsafe {
            let arr_ptr = ptr as *mut RuntimeArray;
            let capacity = (*arr_ptr).capacity as usize;

            // Get pointer to data area (after the header)
            let data_ptr = (arr_ptr as *mut RuntimeArray).add(1) as *mut RuntimeValue;
            let slice = std::slice::from_raw_parts_mut(data_ptr, capacity);

            // Copy data
            for (i, &byte) in data.iter().enumerate() {
                slice[i] = RuntimeValue::from_int(byte as i64);
            }

            // Update length
            (*arr_ptr).len = data.len() as u64;
        }
    }
}

fn read_buffer(buffer: RuntimeValue, len: usize) -> Vec<u8> {
    let mut result = Vec::new();
    if buffer.is_heap() {
        let ptr = buffer.as_heap_ptr();
        unsafe {
            let arr_ptr = ptr as *const RuntimeArray;
            let slice = (*arr_ptr).as_slice();
            for i in 0..len.min((*arr_ptr).len as usize) {
                result.push(slice[i].as_int() as u8);
            }
        }
    }
    result
}

#[test]
fn test_buffer_creation() {
    let buffer = create_buffer(1024);
    assert!(buffer.is_heap(), "Buffer should be heap-allocated");

    println!("✅ Buffer creation test passed!");
}

#[test]
fn test_buffer_write_read() {
    let data = b"Hello, World!";
    let buffer = create_buffer(1024);

    // Write data to buffer
    fill_buffer(buffer, data);

    // Read data from buffer
    let read_data = read_buffer(buffer, data.len());

    assert_eq!(read_data.len(), data.len(), "Length mismatch");
    assert_eq!(&read_data[..], data, "Data mismatch");

    println!("✅ Buffer write/read test passed!");
}

#[test]
fn test_buffer_partial_read() {
    let data = b"Hello, World! This is a longer message.";
    let buffer = create_buffer(1024);

    // Write full data
    fill_buffer(buffer, data);

    // Read only first 13 bytes
    let read_data = read_buffer(buffer, 13);

    assert_eq!(read_data.len(), 13, "Length mismatch");
    assert_eq!(&read_data[..], b"Hello, World!", "Data mismatch");

    println!("✅ Buffer partial read test passed!");
}

#[test]
fn test_buffer_empty() {
    let buffer = create_buffer(1024);

    // Read from empty buffer
    let read_data = read_buffer(buffer, 10);

    assert_eq!(read_data.len(), 0, "Empty buffer should return empty vec");

    println!("✅ Empty buffer test passed!");
}

#[test]
fn test_buffer_binary_data() {
    let data: Vec<u8> = (0..=255).collect();
    let buffer = create_buffer(1024);

    // Write binary data
    fill_buffer(buffer, &data);

    // Read it back
    let read_data = read_buffer(buffer, data.len());

    assert_eq!(read_data.len(), data.len(), "Length mismatch");
    assert_eq!(read_data, data, "Binary data mismatch");

    println!("✅ Binary data test passed!");
}
