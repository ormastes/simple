//! Canonical scoped identities and atomic free claims. Persistent allocations
//! keep the membership-only fast path; only tracked allocations enter `scoped`.
use super::*;
use std::collections::HashMap;
use std::ops::{Deref, DerefMut};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ScopedAllocationKey {
    pub ptr: usize,
    pub birth: u64,
    pub owner: u64,
}

#[derive(Default)]
pub(super) struct HeapRegistry {
    live: HeapPtrSet<usize>,
    pub(super) scoped: HashMap<usize, ScopedAllocationKey, std::hash::BuildHasherDefault<ahash::AHasher>>,
    next_birth: u64,
    next_owner: u64,
}
impl Deref for HeapRegistry {
    type Target = HeapPtrSet<usize>;
    fn deref(&self) -> &Self::Target {
        &self.live
    }
}
impl DerefMut for HeapRegistry {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.live
    }
}

fn advance(counter: &mut u64) -> Option<u64> {
    *counter = counter.checked_add(1)?;
    Some(*counter)
}

pub(crate) fn new_scope_owner() -> Option<u64> {
    advance(&mut heap_allocation_registry().lock().unwrap().next_owner)
}

pub(crate) fn track_scoped_allocation(ptr: usize, owner: u64) -> Option<ScopedAllocationKey> {
    let mut registry = heap_allocation_registry().lock().unwrap();
    if owner == 0 || !registry.contains(&ptr) {
        return None;
    }
    if let Some(key) = registry.scoped.get(&ptr) {
        return (key.owner == owner).then_some(*key);
    }
    // Fail closed on exhaustion. Never mint the same birth twice, including
    // after clear_heap_allocation_registry (which preserves both counters).
    let birth = advance(&mut registry.next_birth)?;
    let key = ScopedAllocationKey { ptr, birth, owner };
    registry.scoped.insert(ptr, key);
    Some(key)
}

pub(crate) fn scoped_key_is_live(key: ScopedAllocationKey) -> bool {
    let registry = heap_allocation_registry().lock().unwrap();
    registry.scoped.get(&key.ptr) == Some(&key) && registry.contains(&key.ptr)
}

/// Install the destination record while canonical source authority is still
/// held. `record` only writes the destination ledger (no runtime callbacks).
/// Source callers tombstone their record only after this succeeds.
pub(crate) fn transfer_scoped_allocation(
    key: ScopedAllocationKey,
    owner: u64,
    record: impl FnOnce(ScopedAllocationKey),
) -> bool {
    let mut registry = heap_allocation_registry().lock().unwrap();
    if registry.scoped.get(&key.ptr) != Some(&key) || !registry.contains(&key.ptr) {
        return false;
    }
    let next = ScopedAllocationKey { owner, ..key };
    record(next);
    if owner == 0 {
        registry.scoped.remove(&key.ptr);
    } else {
        registry.scoped.insert(key.ptr, next);
    }
    true
}

/// Unique retirement authority: deliberately neither Copy nor Clone.
pub(crate) struct ClaimedAllocation {
    pub ptr: *mut HeapHeader,
    pub kind: HeapObjectType,
    pub size: usize,
}
pub(crate) enum ClaimResult {
    Claimed(ClaimedAllocation),
    NotOwned,
    Pinned,
}

fn matches_key(registry: &HeapRegistry, ptr: usize, key: Option<ScopedAllocationKey>) -> bool {
    registry.contains(&ptr) && key.is_none_or(|key| registry.scoped.get(&ptr) == Some(&key))
}

fn claim_locked(
    registry: &mut HeapRegistry,
    ptr: *mut HeapHeader,
    key: Option<ScopedAllocationKey>,
    expected: Option<HeapObjectType>,
    pinned: impl FnOnce() -> bool,
) -> ClaimResult {
    if !matches_key(registry, ptr as usize, key) {
        return ClaimResult::NotOwned;
    }
    // No ledger-derived header read occurs before this exact identity check.
    let header = unsafe { &*ptr };
    if expected.is_some_and(|kind| kind != header.object_type) {
        return ClaimResult::NotOwned;
    }
    if header.object_type == HeapObjectType::String
        && header.reserved & super::super::collections::RT_STRING_FLAG_SHARED != 0
    {
        return ClaimResult::NotOwned;
    }
    if header.object_type == HeapObjectType::Closure && pinned() {
        // The pin table now owns lifetime. A stale scope cannot orphan a later
        // allocation at this address, even if its ledger survives on another thread.
        registry.scoped.remove(&(ptr as usize));
        return ClaimResult::Pinned;
    }
    let claimed = ClaimedAllocation {
        ptr,
        kind: header.object_type,
        size: header.size as usize,
    };
    registry.remove(&(ptr as usize));
    registry.scoped.remove(&(ptr as usize));
    heap_free_epoch_bump();
    ClaimResult::Claimed(claimed)
}

fn claim(ptr: *mut HeapHeader, key: Option<ScopedAllocationKey>, expected: Option<HeapObjectType>) -> ClaimResult {
    let result = if key.is_none() && expected.is_none_or(|kind| kind == HeapObjectType::Closure) {
        // An untyped pointer-only claim cannot revalidate birth across a lock
        // gap. Take pin -> registry before its FIRST observation instead.
        super::super::objects::with_closure_pin_claim(ptr as usize, |defer| {
            let mut registry = heap_allocation_registry().lock().unwrap();
            claim_locked(&mut registry, ptr, key, expected, defer)
        })
    } else {
        let mut registry = heap_allocation_registry().lock().unwrap();
        if !matches_key(&registry, ptr as usize, key) {
            return ClaimResult::NotOwned;
        }
        let kind = unsafe { (*ptr).object_type };
        if expected.is_some_and(|expected| expected != kind) {
            return ClaimResult::NotOwned;
        }
        if kind == HeapObjectType::Closure {
            drop(registry);
            // This path has a scoped key: exact birth+owner revalidation
            // closes the gap while preserving pin -> registry lock order.
            super::super::objects::with_closure_pin_claim(ptr as usize, |defer| {
                let mut registry = heap_allocation_registry().lock().unwrap();
                claim_locked(&mut registry, ptr, key, expected, defer)
            })
        } else {
            let result = claim_locked(&mut registry, ptr, key, expected, || false);
            drop(registry);
            result
        }
    };
    if let ClaimResult::Claimed(ref allocation) = result {
        let kind = allocation.kind as u8;
        let bytes = allocation.size as u64;
        super::super::dict_scope_read::unregistered(ptr as usize, kind);
        note_heap_free(kind, bytes);
        note_attr_free(ptr as usize, bytes);
        super::super::collections::transient_promote_share_forget(ptr as usize);
    }
    result
}

pub(crate) fn claim_free(ptr: *mut HeapHeader) -> ClaimResult {
    claim(ptr, None, None)
}
pub(crate) fn claim_scoped_free(key: ScopedAllocationKey) -> ClaimResult {
    claim(key.ptr as *mut HeapHeader, Some(key), None)
}
pub(crate) fn claim_typed_free(value: super::super::RuntimeValue, kind: HeapObjectType) -> ClaimResult {
    if !value.is_heap() {
        return ClaimResult::NotOwned;
    }
    claim(value.as_heap_ptr(), None, Some(kind))
}

#[cfg(test)]
#[path = "heap_claim_tests.rs"]
mod tests;
