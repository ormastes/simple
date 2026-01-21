use crate::NoGcAllocator;
use simple_common::gc::GcAllocator;

#[test]
fn no_gc_allocator_allocates_without_tracing() {
    let alloc = NoGcAllocator::new();
    let ptr = alloc.alloc_bytes(&[1u8, 2, 3, 4]);
    assert_ne!(ptr, 0);
    alloc.collect(); // should be a no-op
}
