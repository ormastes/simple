//! SMF Linker Tests
//!
//! Tests for Settlement linker functionality

use simple_loader::settlement::{ModuleHandle, SettlementLinker};

// =============================================================================
// ModuleHandle Tests
// =============================================================================

#[test]
fn test_module_handle_valid() {
    let handle = ModuleHandle(0);
    assert!(handle.is_valid());

    let handle = ModuleHandle(1);
    assert!(handle.is_valid());

    let handle = ModuleHandle(100);
    assert!(handle.is_valid());
}

#[test]
fn test_module_handle_invalid() {
    let handle = ModuleHandle::INVALID;
    assert!(!handle.is_valid());
    assert_eq!(handle.0, u32::MAX);
}

#[test]
fn test_module_handle_as_usize() {
    let handle = ModuleHandle(42);
    assert_eq!(handle.as_usize(), 42);

    let handle = ModuleHandle(0);
    assert_eq!(handle.as_usize(), 0);

    let handle = ModuleHandle(1000);
    assert_eq!(handle.as_usize(), 1000);
}

#[test]
fn test_module_handle_equality() {
    let handle1 = ModuleHandle(10);
    let handle2 = ModuleHandle(10);
    let handle3 = ModuleHandle(20);

    assert_eq!(handle1, handle2);
    assert_ne!(handle1, handle3);
}

#[test]
fn test_module_handle_clone() {
    let handle = ModuleHandle(55);
    let cloned = handle.clone();

    assert_eq!(handle, cloned);
    assert_eq!(cloned.0, 55);
}

#[test]
fn test_module_handle_copy() {
    let handle = ModuleHandle(77);
    let copied = handle;

    assert_eq!(handle, copied);
    assert_eq!(copied.0, 77);
}

#[test]
fn test_module_handle_hash() {
    use std::collections::HashMap;

    let mut map = HashMap::new();
    let handle1 = ModuleHandle(1);
    let handle2 = ModuleHandle(2);

    map.insert(handle1, "module1");
    map.insert(handle2, "module2");

    assert_eq!(map.get(&handle1), Some(&"module1"));
    assert_eq!(map.get(&handle2), Some(&"module2"));
}

// =============================================================================
// SettlementLinker Tests
// =============================================================================

#[test]
fn test_settlement_linker_new() {
    let linker = SettlementLinker::new();
    // Should create without panic
    drop(linker);
}

#[test]
fn test_settlement_linker_default() {
    let linker = SettlementLinker::default();
    // Should create without panic using default
    drop(linker);
}
