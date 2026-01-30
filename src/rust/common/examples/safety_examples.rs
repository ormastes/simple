//! Safety Infrastructure Examples
//!
//! This file demonstrates practical usage of the safety infrastructure.
//! Run with: cargo run --example safety_examples -p simple-common

use simple_common::{
    safe_add, safe_sub, safe_mul, safe_div,
    safe_index, safe_index_signed,
    safe_char_at, safe_substring,
    to_usize, to_i64,
    ArithmeticError, IndexError, StringError,
};

fn main() {
    println!("=== Safety Infrastructure Examples ===\n");

    example_arithmetic();
    example_indexing();
    example_conversions();
    example_strings();
}

fn example_arithmetic() {
    println!("1. Safe Arithmetic Operations");
    println!("------------------------------");

    // Success case
    match safe_add(100, 200) {
        Ok(result) => println!("✅ 100 + 200 = {}", result),
        Err(e) => println!("❌ Error: {}", e),
    }

    // Overflow case
    match safe_add(i32::MAX, 1) {
        Ok(result) => println!("✅ Result: {}", result),
        Err(e) => println!("❌ Overflow detected: {}", e),
    }

    // Division by zero
    match safe_div(10, 0) {
        Ok(result) => println!("✅ Result: {}", result),
        Err(e) => println!("❌ Division by zero: {}", e),
    }

    // Underflow
    match safe_sub(0u32, 1u32) {
        Ok(result) => println!("✅ Result: {}", result),
        Err(e) => println!("❌ Underflow detected: {}", e),
    }

    println!();
}

fn example_indexing() {
    println!("2. Safe Array Indexing");
    println!("---------------------");

    let arr = [10, 20, 30, 40, 50];

    // Success case
    match safe_index(&arr, 2) {
        Ok(value) => println!("✅ arr[2] = {}", value),
        Err(e) => println!("❌ Error: {}", e),
    }

    // Out of bounds
    match safe_index(&arr, 10) {
        Ok(value) => println!("✅ Value: {}", value),
        Err(e) => println!("❌ Index error: {}", e),
    }

    // Negative indexing (Python-style)
    match safe_index_signed(&arr, -1) {
        Ok(value) => println!("✅ arr[-1] = {} (last element)", value),
        Err(e) => println!("❌ Error: {}", e),
    }

    match safe_index_signed(&arr, -2) {
        Ok(value) => println!("✅ arr[-2] = {} (second-to-last)", value),
        Err(e) => println!("❌ Error: {}", e),
    }

    // Negative out of bounds
    match safe_index_signed(&arr, -10) {
        Ok(value) => println!("✅ Value: {}", value),
        Err(e) => println!("❌ Negative index error: {}", e),
    }

    println!();
}

fn example_conversions() {
    println!("3. Safe Type Conversions");
    println!("-----------------------");

    // Success case
    match to_usize(42i32) {
        Ok(value) => println!("✅ 42i32 -> usize = {}", value),
        Err(e) => println!("❌ Error: {}", e),
    }

    // Negative to unsigned
    match to_usize(-1i32) {
        Ok(value) => println!("✅ Value: {}", value),
        Err(e) => println!("❌ Cannot convert negative to unsigned: {}", e),
    }

    // Overflow
    match to_i64(u128::MAX) {
        Ok(value) => println!("✅ Value: {}", value),
        Err(e) => println!("❌ Conversion overflow: {}", e),
    }

    println!();
}

fn example_strings() {
    println!("4. Safe String Operations (UTF-8)");
    println!("----------------------------------");

    let s = "Hello 🌍 World";

    // Character indexing
    match safe_char_at(s, 0) {
        Ok(c) => println!("✅ s[0] = '{}' (character)", c),
        Err(e) => println!("❌ Error: {}", e),
    }

    // Multi-byte character (emoji)
    match safe_char_at(s, 6) {
        Ok(c) => println!("✅ s[6] = '{}' (emoji)", c),
        Err(e) => println!("❌ Error: {}", e),
    }

    // Out of bounds
    match safe_char_at(s, 100) {
        Ok(c) => println!("✅ Character: {}", c),
        Err(e) => println!("❌ Character index error: {}", e),
    }

    // Substring extraction
    match safe_substring(s, 0, 5) {
        Ok(substr) => println!("✅ s[0..5] = \"{}\"", substr),
        Err(e) => println!("❌ Error: {}", e),
    }

    match safe_substring(s, 6, 7) {
        Ok(substr) => println!("✅ s[6..7] = \"{}\" (emoji only)", substr),
        Err(e) => println!("❌ Error: {}", e),
    }

    println!();
}

// Real-world example: Computing array sizes safely
fn compute_buffer_size(width: i64, height: i64, bytes_per_pixel: usize) -> Result<usize, String> {
    // Step 1: Multiply dimensions
    let pixel_count = safe_mul(width, height)
        .map_err(|e| format!("Dimension overflow: {}", e))?;

    // Step 2: Convert to usize
    let pixel_count_usize = to_usize(pixel_count)
        .map_err(|e| format!("Pixel count conversion failed: {}", e))?;

    // Step 3: Multiply by bytes per pixel
    let total_bytes = safe_mul(pixel_count_usize, bytes_per_pixel)
        .map_err(|e| format!("Buffer size overflow: {}", e))?;

    Ok(total_bytes)
}

#[test]
fn test_real_world_example() {
    // Normal case
    let size = compute_buffer_size(1920, 1080, 4).unwrap();
    assert_eq!(size, 1920 * 1080 * 4);

    // Overflow case
    let result = compute_buffer_size(i64::MAX, i64::MAX, 4);
    assert!(result.is_err());
    println!("Overflow properly detected: {}", result.unwrap_err());
}
