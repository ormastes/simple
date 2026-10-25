use super::*;

fn live(value: RuntimeValue) -> bool {
    super::super::heap::is_registered_heap_ptr(value.as_heap_ptr())
}

#[test]
fn session_end_ignores_controlled_same_address_persistent_rebirth() {
    let session = rt_session_heap_begin();
    assert_ne!(session, 0);
    let value = rt_array_new(8);
    assert!(session_heap_owns(value));
    // Keep backing storage reserved while rotating canonical registry lifetime.
    // This deterministically reproduces the stale ledger without allocator luck.
    let allocation = match claim_free(value.as_heap_ptr()) {
        ClaimResult::Claimed(allocation) => allocation,
        _ => panic!("claim"),
    };
    register_heap_ptr(allocation.ptr);
    assert!(!session_heap_owns(value), "pointer bits are not ownership");
    assert!(rt_session_heap_end(session));
    assert!(live(value));
    rt_array_free(value);
    assert!(!live(value));
}

#[test]
fn foreign_thread_claim_rebirth_survives_old_session_end() {
    let session = rt_session_heap_begin();
    assert_ne!(session, 0);
    let value = rt_array_new(8);
    let bits = value.0;
    let (ready_tx, ready_rx) = std::sync::mpsc::channel();
    let (end_tx, end_rx) = std::sync::mpsc::channel();
    let worker = std::thread::spawn(move || {
        let value = RuntimeValue(bits);
        let allocation = match claim_free(value.as_heap_ptr()) {
            ClaimResult::Claimed(allocation) => allocation,
            _ => panic!("claim"),
        };
        let other = rt_session_heap_begin();
        assert_ne!(other, 0);
        register_heap_ptr(allocation.ptr);
        track_transient_heap(value);
        ready_tx.send(()).unwrap();
        end_rx.recv().unwrap();
        assert!(session_heap_owns(value));
        assert!(live(value));
        assert!(rt_session_heap_end(other));
        assert!(!live(value));
    });
    ready_rx.recv().unwrap();
    assert!(!session_heap_owns(value));
    assert!(rt_session_heap_end(session));
    end_tx.send(()).unwrap();
    worker.join().unwrap();
}

#[test]
fn module_transfer_retires_source_identity_and_session_releases_once() {
    let session = rt_session_heap_begin();
    assert_ne!(session, 0);
    assert!(rt_transient_array_scope_begin());
    let value = rt_array_new(8);
    let source = TRANSIENT_HEAP_SCOPE.with(|slot| slot.borrow().as_ref().unwrap().objects[0]);
    assert!(rt_transient_array_scope_pause());
    assert!(rt_transient_heap_adopt(value));
    assert!(matches!(claim_scoped_free(source), ClaimResult::NotOwned));
    assert!(rt_transient_array_scope_end());
    assert!(session_heap_owns(value));
    assert!(rt_session_heap_end(session));
    assert!(!live(value));
    rt_array_free(value); // Alias must not dispose aux a second time.
}

#[test]
fn session_pinned_closure_outlives_scope_until_last_release() {
    let session = rt_session_heap_begin();
    assert_ne!(session, 0);
    let value = super::super::objects::rt_closure_new(std::ptr::null(), 0);
    assert_eq!(super::super::objects::rt_closure_retain(value), 1);
    assert!(rt_session_heap_end(session));
    assert!(live(value));
    assert_eq!(super::super::objects::rt_closure_release(value), 1);
    assert!(!live(value));
    assert_eq!(super::super::objects::rt_closure_release(value), 0);
}

#[test]
fn typed_frees_leave_no_canonical_session_authority() {
    let session = rt_session_heap_begin();
    assert_ne!(session, 0);
    let array = rt_array_new(4);
    let tuple = rt_tuple_new(3);
    let dict = super::super::dict::rt_dict_new(4);
    let object = super::super::objects::rt_object_new(42, 2);
    let closure = super::super::objects::rt_closure_new(std::ptr::null(), 0);
    let text = b"uncached identity regression";
    let string = rt_string_new(text.as_ptr(), text.len() as u64);
    rt_array_free(array);
    rt_tuple_free(tuple);
    super::super::dict::rt_dict_free(dict);
    super::super::objects::rt_object_free(object);
    super::super::objects::rt_closure_free(closure);
    assert_eq!(rt_string_free(string), 1);
    for value in [array, tuple, dict, object, closure, string] {
        assert!(!session_heap_owns(value));
        assert!(!live(value));
    }
    assert!(rt_session_heap_end(session));
}
