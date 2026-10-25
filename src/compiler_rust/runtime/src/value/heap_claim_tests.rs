use super::*;
use crate::value::collections::{dispose_claimed, rt_array_new};

fn claimed(result: ClaimResult) -> ClaimedAllocation {
    match result {
        ClaimResult::Claimed(allocation) => allocation,
        _ => panic!("expected unique claim"),
    }
}

// Registry-controlled reuse: retain the allocated storage after retirement and
// register that exact address as a new allocation lifetime. No allocator luck.
fn rebirth(old: ClaimedAllocation, owner: u64) -> ScopedAllocationKey {
    let ptr = old.ptr;
    register_heap_ptr(ptr);
    track_scoped_allocation(ptr as usize, owner).unwrap()
}

#[test]
fn same_address_new_birth_rejects_stale_key() {
    let value = rt_array_new(4);
    let owner = new_scope_owner().unwrap();
    let old = track_scoped_allocation(value.as_heap_ptr() as usize, owner).unwrap();
    let next = rebirth(claimed(claim_free(value.as_heap_ptr())), owner);
    assert_eq!(old.ptr, next.ptr);
    assert_ne!(old.birth, next.birth);
    assert!(matches!(claim_scoped_free(old), ClaimResult::NotOwned));
    assert!(scoped_key_is_live(next));
    dispose_claimed(claimed(claim_scoped_free(next)));
    assert!(matches!(claim_scoped_free(next), ClaimResult::NotOwned));
}

#[test]
fn foreign_thread_free_and_same_address_foreign_owner_are_canonical() {
    let value = rt_array_new(4);
    let old = track_scoped_allocation(value.as_heap_ptr() as usize, new_scope_owner().unwrap()).unwrap();
    let next = std::thread::spawn(move || {
        let allocation = claimed(claim_free(old.ptr as *mut HeapHeader));
        rebirth(allocation, new_scope_owner().unwrap())
    })
    .join()
    .unwrap();
    assert_eq!(old.ptr, next.ptr);
    assert_ne!(old.birth, next.birth);
    assert_ne!(old.owner, next.owner);
    assert!(!scoped_key_is_live(old));
    assert!(matches!(claim_scoped_free(old), ClaimResult::NotOwned));
    dispose_claimed(claimed(claim_scoped_free(next)));
}

#[test]
fn transfer_installs_destination_before_source_withdrawal() {
    let value = rt_array_new(0);
    let source = track_scoped_allocation(value.as_heap_ptr() as usize, new_scope_owner().unwrap()).unwrap();
    let owner = new_scope_owner().unwrap();
    let mut destination = None;
    assert!(transfer_scoped_allocation(source, owner, |key| destination = Some(key)));
    let destination = destination.unwrap();
    assert_eq!(destination.birth, source.birth);
    assert_eq!(destination.owner, owner);
    assert!(matches!(claim_scoped_free(source), ClaimResult::NotOwned));
    assert!(scoped_key_is_live(destination));
    let mut called = false;
    assert!(!transfer_scoped_allocation(source, owner, |_| called = true));
    assert!(!called, "stale source cannot install a destination");
    dispose_claimed(claimed(claim_scoped_free(destination)));
}

#[test]
fn stale_identity_rejected_before_header_dereference() {
    // This address is deliberately not mapped. Only membership/key comparison
    // is legal; a header read would fault instead of returning NotOwned.
    let key = ScopedAllocationKey {
        ptr: 0x1000,
        birth: u64::MAX,
        owner: u64::MAX,
    };
    assert!(matches!(claim_scoped_free(key), ClaimResult::NotOwned));
}

#[test]
fn exhausted_identity_counter_never_wraps() {
    let mut counter = u64::MAX - 1;
    assert_eq!(advance(&mut counter), Some(u64::MAX));
    assert_eq!(advance(&mut counter), None);
    assert_eq!(advance(&mut counter), None);
    assert_eq!(counter, u64::MAX);
}

#[test]
fn persistent_registry_has_no_scoped_record_and_claim_is_once() {
    let value = rt_array_new(4);
    {
        let registry = heap_allocation_registry().lock().unwrap();
        assert!(!registry.scoped.contains_key(&(value.as_heap_ptr() as usize)));
    }
    let allocation = claimed(claim_free(value.as_heap_ptr()));
    assert!(matches!(claim_free(value.as_heap_ptr()), ClaimResult::NotOwned));
    dispose_claimed(allocation);
}

#[test]
fn stale_closure_key_cannot_orphan_new_pinned_lifetime() {
    use crate::value::objects::{rt_closure_new, rt_closure_release, rt_closure_retain};
    let value = rt_closure_new(std::ptr::null(), 0);
    let old = track_scoped_allocation(value.as_heap_ptr() as usize, new_scope_owner().unwrap()).unwrap();
    let next = rebirth(claimed(claim_free(value.as_heap_ptr())), new_scope_owner().unwrap());
    assert_eq!(rt_closure_retain(value), 1);
    assert!(matches!(claim_scoped_free(old), ClaimResult::NotOwned));
    assert_eq!(rt_closure_release(value), 1);
    assert!(scoped_key_is_live(next), "stale claim must not orphan the new pin");
    dispose_claimed(claimed(claim_scoped_free(next)));
    assert_eq!(rt_closure_retain(value), 0, "retain after claim cannot publish a pin");
}

#[test]
fn scoped_bookkeeping_layout_reports_real_payload_cost() {
    assert_eq!(std::mem::size_of::<ScopedAllocationKey>(), 24);
    eprintln!("scoped-claim-cost: pointer_bytes={} key_bytes={} canonical_map_entry_bytes={} session_map_entry_bytes={} module_index_entry_bytes={}; HashMap load/control/allocator overhead and Vec spare capacity are additional", 
        std::mem::size_of::<usize>(), std::mem::size_of::<ScopedAllocationKey>(),
        std::mem::size_of::<(usize, ScopedAllocationKey)>(),
        std::mem::size_of::<(usize, ScopedAllocationKey)>(),
        std::mem::size_of::<(usize, usize)>());
}
