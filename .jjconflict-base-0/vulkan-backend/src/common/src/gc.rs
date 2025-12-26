/// GC allocator contract for compiler/runtime boundary.
pub trait GcAllocator {
    /// Allocate bytes for a value; returns an opaque handle.
    fn alloc_bytes(&self, bytes: &[u8]) -> usize;

    /// Trigger a collection cycle (optional).
    fn collect(&self);
}

/// Marker trait for GC-managed handles.
pub trait GcHandle {}
