use simple_common::gc::GcAllocator;
use crate::gc::GcRuntime;

#[test]
fn allocator_contract_allocates_and_collects() {
    let gc = GcRuntime::new();
    let allocator: &dyn GcAllocator = &gc;

    let handle = allocator.alloc_bytes(&[1u8, 2, 3, 4]);
    assert_ne!(handle, 0, "allocator should return a non-null handle");

    // Should be safe to trigger a manual collection via the trait.
    allocator.collect();
}
