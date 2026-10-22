# MonoCache restore accounting and replacement eviction

Baseline: release_phase3 `30e9aa83e94f557137dbceae22b27973d125d625`. Requirement: generic formal hardening plan §7.

Confirmed source defect: `MonoCache.load_from_disk` restored persisted dictionary rows but left the constructor's count zero and oldest key empty. Subsequent capacity checks could therefore permit more retained rows than the trusted cap. `store` also evicted at capacity before checking whether the write merely replaced an existing key.

The scoped repair derives cardinality from unique decoded nonempty keys, keeps the existing last-row-wins duplicate policy, refuses a first unique row beyond trusted persistent capacity to the existing empty-cache fallback, and computes the persisted minimum once after duplicate updates settle. Persisted max_entries and entry_count remain ignored. Store checks replacement before eviction and refuses inserts when capacity is nonpositive. No cache layout fields, clock, wire format or public API changed.

Scope limits: persisted entries remain metadata with nil specialization values. Metadata lookup hit accounting, synthetic timestamps, true LRU behavior, SDN string escaping, whole-file decoder memory limits and externally mutated public cache internals remain separate pre-existing concerns. No new hot-path scan is introduced. Existing full-capacity eviction remains O(k) with dictionary rebuilding; its old O(1)-amortized comment is not a performance proof. This change does not claim to fix those wider issues.

Pinned compiler source references show only the MonoCache owner and its facade export; no active compiler integration caller was found in the finite exact-source reference search. This is a cache-owner correctness prerequisite, not a Phase3 speedup or demonstrated production active-path repair.

Eleven real SSpec scenarios replace the old placeholder and obsolete commented integer-valued store calls. Source authored first; compiler/tests/docgen/native/perf/RSS all UNRUN. The source-review packet retains baseline and after hashes; independent review remains required. No runtime/build/seed/commit/push performed by the author.

Cycle2 CACHE-RESTORE-001: replacing the recorded minimum invalidates its marker. An empty marker on a populated table stays unknown across intervening inserts/replacements, and the existing eviction fallback discovers the minimum only when needed. Empty-table insertion reestablishes the marker, including after singleton eviction. Three additional production API scenarios prove oldest replacement, intervening writes and singleton behavior; all UNRUN. No extra per-store scan or new clock/field is introduced. Existing synthetic timestamp and lookup-aging limitations remain.
