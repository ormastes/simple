// NONLOCAL-OVERLAY: the `nonlocal_overlay` superset must never MISS an overlay
// key that `is_local` does not cover.
//
// The call-entry global publish (`publish_live_bound_globals`) iterates the
// superset instead of the whole overlay, so a missing name is a global write
// silently dropped — not a slow path, a wrong answer. `nonlocal_overlay_audit_misses`
// is the invariant's own oracle: it recomputes the exact set from the overlay
// and reports what the superset failed to cover, and must be empty after every
// mutation ordering below. (Over-approximation is safe by construction and is
// therefore NOT asserted against.)

#[test]
fn nonlocal_overlay_superset_covers_every_mutation_ordering() {
    let v = || Value::Int(1);

    // plain insert
    let mut env = CowEnv::new();
    env.insert("a".into(), v());
    assert!(env.nonlocal_overlay_audit_misses().is_empty(), "insert");
    assert_eq!(env.nonlocal_overlay_entries().count(), 1);

    // mark_local AFTER insert: the name drops out of the publishable set
    env.mark_local("a");
    assert!(env.nonlocal_overlay_audit_misses().is_empty(), "insert->mark_local");
    assert_eq!(env.nonlocal_overlay_entries().count(), 0);

    // mark_local BEFORE insert: never enters the set
    let mut env = CowEnv::new();
    env.mark_local("b");
    env.insert("b".into(), v());
    assert!(env.nonlocal_overlay_audit_misses().is_empty(), "mark_local->insert");
    assert_eq!(env.nonlocal_overlay_entries().count(), 0);

    // block-local shadow: out while shadowed, BACK when the block exits
    let mut env = CowEnv::new();
    env.insert("c".into(), v());
    env.enter_block_local("c");
    assert_eq!(env.nonlocal_overlay_entries().count(), 0, "shadowed");
    assert!(env.nonlocal_overlay_audit_misses().is_empty());
    env.exit_block_local("c");
    assert!(env.nonlocal_overlay_audit_misses().is_empty(), "block exit");
    assert_eq!(env.nonlocal_overlay_entries().count(), 1, "publishable again");

    // nested block depth: one exit must NOT unshadow
    let mut env = CowEnv::new();
    env.insert("d".into(), v());
    env.enter_block_local("d");
    env.enter_block_local("d");
    env.exit_block_local("d");
    assert_eq!(env.nonlocal_overlay_entries().count(), 0, "still shadowed");
    env.exit_block_local("d");
    assert_eq!(env.nonlocal_overlay_entries().count(), 1);
    assert!(env.nonlocal_overlay_audit_misses().is_empty());

    // a frame-local name must not come back publishable when a block exits
    let mut env = CowEnv::new();
    env.insert("e".into(), v());
    env.mark_local("e");
    env.enter_block_local("e");
    env.exit_block_local("e");
    assert_eq!(env.nonlocal_overlay_entries().count(), 0, "declared local");
    assert!(env.nonlocal_overlay_audit_misses().is_empty());

    // remove / re-insert
    let mut env = CowEnv::new();
    env.insert("f".into(), v());
    env.remove("f");
    assert_eq!(env.nonlocal_overlay_entries().count(), 0);
    env.insert("f".into(), v());
    assert!(env.nonlocal_overlay_audit_misses().is_empty(), "reinsert");
    assert_eq!(env.nonlocal_overlay_entries().count(), 1);

    // take_frame_owned / restore_frame_owned
    let mut env = CowEnv::new();
    env.insert("g".into(), v());
    let taken = env.take_frame_owned("g").expect("frame-owned");
    assert_eq!(env.nonlocal_overlay_entries().count(), 0);
    env.restore_frame_owned("g".into(), taken);
    assert!(env.nonlocal_overlay_audit_misses().is_empty(), "restore");
    assert_eq!(env.nonlocal_overlay_entries().count(), 1);

    // entry() may insert without going through insert()
    let mut env = CowEnv::new();
    env.entry("h".into()).or_insert_with(v);
    assert!(env.nonlocal_overlay_audit_misses().is_empty(), "entry");
    assert_eq!(env.nonlocal_overlay_entries().count(), 1);

    // get_mut promotes a shared-base name into the overlay
    let mut base = HashMap::new();
    base.insert("i".to_string(), v());
    let mut env = CowEnv::with_base(Arc::new(base));
    assert_eq!(env.nonlocal_overlay_entries().count(), 0, "not yet promoted");
    env.get_mut("i").expect("promote");
    assert!(env.nonlocal_overlay_audit_misses().is_empty(), "get_mut");
    assert_eq!(env.nonlocal_overlay_entries().count(), 1);

    // refresh_globals inserts without marking a frame write
    let mut env = CowEnv::new();
    env.refresh_globals([("j".to_string(), v())]);
    assert!(env.nonlocal_overlay_audit_misses().is_empty(), "refresh_globals");

    // extend / clear
    let mut env = CowEnv::new();
    env.extend([("k".to_string(), v()), ("l".to_string(), v())]);
    assert!(env.nonlocal_overlay_audit_misses().is_empty(), "extend");
    assert_eq!(env.nonlocal_overlay_entries().count(), 2);
    env.clear();
    assert_eq!(env.nonlocal_overlay_entries().count(), 0, "clear");
    assert!(env.nonlocal_overlay_audit_misses().is_empty());

    // from_map: nothing is local, so every key is publishable
    let mut map = HashMap::new();
    map.insert("m".to_string(), v());
    map.insert("n".to_string(), v());
    let env = CowEnv::from_map(map);
    assert!(env.nonlocal_overlay_audit_misses().is_empty(), "from_map");
    assert_eq!(env.nonlocal_overlay_entries().count(), 2);

    // clone carries the superset
    let cloned = env.clone();
    assert!(cloned.nonlocal_overlay_audit_misses().is_empty(), "clone");
    assert_eq!(cloned.nonlocal_overlay_entries().count(), 2);
}

// The publishable set must equal what the old whole-overlay walk produced.
// Built as a mixed frame — locals, a block shadow, a refreshed global and a
// plain alias — and compared against the predicate applied to the overlay.
#[test]
fn nonlocal_overlay_entries_match_the_overlay_walk_it_replaced() {
    let mut env = CowEnv::new();
    for name in ["p1", "p2", "p3", "alias", "shadowed", "refreshed"] {
        env.insert(name.to_string(), Value::Int(7));
    }
    env.mark_local("p1");
    env.mark_local("p2");
    env.mark_local("p3");
    env.enter_block_local("shadowed");
    env.refresh_globals([("refreshed".to_string(), Value::Int(9))]);

    let mut want: Vec<String> = env
        .overlay_entries()
        .filter(|(name, _)| !env.is_local(name))
        .map(|(name, _)| name.clone())
        .collect();
    let mut got: Vec<String> = env
        .nonlocal_overlay_entries()
        .map(|(name, _)| name.clone())
        .collect();
    want.sort();
    got.sort();
    assert_eq!(got, want, "superset-driven set diverged from the overlay walk");
    assert!(!got.is_empty(), "fixture must produce a non-empty set");
    assert!(env.nonlocal_overlay_audit_misses().is_empty());
}
