// A non-owner thread resolving a layered `ModuleBindings` chain must walk it
// once, not twice per level. The doubled walk was 2^depth and made every
// global/method lookup on a worker thread take seconds (or overflow).
// doc/08_tracking/bug/seed_thread_shared_class_object_crash_2026-11-23.md

fn ftb_chain(depth: usize) -> Arc<ModuleBindings> {
    let mut own = DictMap::new();
    own.insert("x".to_string(), Value::Int(1));
    let names = Arc::new(ModuleTable::new(Arc::new(own), Vec::new()));
    let mut root = ModuleBindings::default();
    root.insert("x".to_string(), (Arc::from("root"), "x".to_string()));
    let mut current = Arc::new(root);
    for level in 0..depth {
        let mut next = ModuleBindings::default();
        // Two layers over the same source: the shape of a diamond import.
        next.push_layer(Arc::from(format!("m{level}a").as_str()), Arc::clone(&names), Some(Arc::clone(&current)));
        next.push_layer(Arc::from(format!("m{level}b").as_str()), Arc::clone(&names), Some(Arc::clone(&current)));
        current = Arc::new(next);
    }
    current
}

#[test]
fn foreign_thread_layered_binding_lookup_is_linear_in_depth() {
    // Depth 40: the doubled walk is 2^40 layer probes (never finishes); the
    // single walk is a few hundred. A deadline turns the old hang into a FAIL.
    let top = ftb_chain(40);
    let owner_answer = top.get("x").map(|b| b.into_owned());
    assert_eq!(owner_answer, Some((Arc::from("root"), "x".to_string())));
    // Stress: many foreign threads resolve concurrently through the shared
    // chain while none of them owns any memo.
    let (tx, rx) = std::sync::mpsc::channel();
    for _ in 0..8 {
        let shared = Arc::clone(&top);
        let tx = tx.clone();
        std::thread::spawn(move || {
            for _ in 0..200 {
                let got = shared.get("x").map(|b| b.into_owned());
                if tx.send(got).is_err() {
                    return;
                }
            }
        });
    }
    drop(tx);
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(20);
    for _ in 0..(8 * 200) {
        let left = deadline.saturating_duration_since(std::time::Instant::now());
        let got = rx.recv_timeout(left).expect("foreign-thread lookup exceeded 20s deadline (exponential walk)");
        assert_eq!(got, owner_answer);
    }
}
