# Agent Tasks: SFFI v2 Hardening

**Status:** P0/P1 implementation handoff; P4+ planned

## Frozen before fan-out

The primary/highest-capability owner freezes `SffiFunctionContractV2`,
`ReturnOrigin`, return families, `ForeignRaw`, error codes, ABI encoding,
system-spec helper names, and manual step text from the detail design. No agent
creates a private duplicate.

| Lane | Scope | Sidecar | Acceptance owner |
|---|---|---|---|
| A0 | schema, diagnostics, golden encodings | Codex Spark for census only | merge owner |
| A1 | Rust seed return and interpreter extern semantics | Claude Haiku for fixture inventory | merge owner |
| A2 | self-hosted frontend/HIR/semantics | Codex Spark for reference search | merge owner |
| A3 | generator and C/C++/Rust wrapper shapes | Claude Sonnet draft review | merge owner |
| A5 | JIT/native/linker/SimpleOS P0 closure | Codex Spark for lane census | merge owner |
| A7 | reproduce-first, system scenarios, parity | Claude Haiku for matrix census | final reviewer |
| P4–P6 | evidence, migration, full performance | planned; no sidecar starts yet | separately assigned |

Sidecars may inventory and draft bounded slices. They may not approve exclusions,
manual quality, generated evidence, or done marks.

## Integration order

1. A0 interface freeze and golden vectors.
2. A1/A2/A3 in non-overlapping owner files.
3. A5 consumes the frozen registry and error contract.
4. A7 reruns only previously RED/changed shards, then one authoritative matrix.
5. Documentation/bug records update from measured evidence.

## Ownership and review

- **Merge owner:** `/root` (or an explicitly reassigned primary agent).
- **Final reviewer:** best available normal/highest-capability Codex, independent
  of lower-model sidecar drafts.
- **Docs owner:** `/root/docs_specs` for this artifact set only.
- **Concurrent-work rule:** each implementation agent uses a separate worktree,
  commits only owned files, and reports unrelated dirt without folding it in.

Maximum three verify/fix cycles per phase. A lane with unavailable tooling
records a fail-fast blocker; it does not substitute seed/static evidence or a
passing placeholder.

## Current continuation sequence

1. Harden the three raw pointer-write providers and register exact void ABIs.
2. Enforce exact pointer-write declarations with a source audit; migrate all
   false return types and widened i32 payloads.
3. Add contract-bearing unsafe metadata and narrow `unsafe(ffi, raw_ptr)` call
   scopes, prioritizing wrappers that already establish allocation bounds.
4. Rebuild the contract inventory and migrate the next highest-risk uncovered
   runtime family.
5. Gate each slice with focused behavior, ABI, source, lint, and hot-path shape
   checks; do not repeat an already-green check in the same session.
6. Treat signing as separate artifact-admission evidence. Never label a
   provider semantically verified merely because its artifact is signed.
7. Linux `spl_winit` admission uses an open-file descriptor for both hashing
   and `dlopen`, with no hot-call work. Extend immutable-handle loading to
   other supported platforms before granting their sealed providers the same
   artifact-identity assurance.
8. Continue the inventory by replacing remaining sentinel/nullable raw ABIs
   with generated typed contracts and proof/test receipts; full SFFI remains
   incomplete until every execution lane consumes the authoritative registry.
9. Cocoa C/Rust providers and their Simple consumer are now fail-closed for
   fabricated presentation/blur success, invalid strings, and allocation
   arithmetic. Before `Verified`, run macOS real-provider race/sanitizer tests,
   bind the selected provider artifact, and replace ambiguous pixel/event
   sentinels with typed results.
10. Canonical `rt_sdl2_*` now owns O(1) generation-checked window resources,
    owner-thread gating, and validated pixel descriptors; app duplication is
    collapsed. Next replace the library owner's 66 generic unsafe contracts
    with exact per-function metadata and lexical wrapper scopes, then bind the
    dynamically loaded SDL artifact and sanitizer receipts before `Verified`.
11. SDL2 display discovery now returns typed absence instead of fabricated
    names/DPI/bounds and all 11 declarations have exact sentinels. Continue
    through the canonical event/input/clipboard declarations, then implement
    signed admission for the dynamically loaded SDL artifact.
12. SDL2 clipboard read/query now preserve provider failure as typed absence,
    strict UTF-8 lifting, and `Result`, with a reusable shutdown-owned cache and
    no extra hot-path call. Replace the two explicitly unsafe legacy plain
    adapters, migrate remaining event/input declarations, and bind signed
    artifact plus sanitizer evidence before classifying SDL2 as verified.
13. SDL2 cached-event details now have exact precondition/lifetime contracts
    and nine safe wrappers use minimal lexical FFI scopes without changing the
    O(1), zero-allocation hot path. Next replace poll/wait's ambiguous zero
    sentinel with typed status and migrate its raw compatibility consumers;
    keep those adapters unsafe until that migration is complete.
14. SDL2 poll/wait now reserve negative status for provider failure, lift it
    into `EventBatch.is_valid`, and disable direct consumers after failure with
    no extra native call. Next distinguish SDL wait timeout from SDL internal
    error and replace the remaining integer compatibility adapter with a typed
    result before treating event admission as safe.
15. SDL2 polled key/button/coordinate functions now use disjoint failure
    sentinels and safe optional wrappers with unchanged native-call counts.
    Continue through time, quit-state, and window-property declarations, then
    bind signed provider and sanitizer receipts before verification status.
16. SDL2 clocks now reserve negative provider failure, saturate nanosecond
    overflow, and expose safe optional wrappers; Web UI stops rather than spins
    on loss. Continue with quit state and window properties, then attach signed
    artifact and runtime verification evidence.
17. Six SDL2 window mutations now return generation-checked status across C,
    Rust dispatch, and Simple; compositor resize commits only after success and
    the hot path is unchanged. Continue through remaining size/position reads,
    lifecycle, cursor, and property contracts before signed provider admission.
18. SDL2 size/position reads now use disjoint invalid-handle sentinels and
    optional wrappers without extra native calls. Continue through lifecycle,
    cursor, flag, and remaining property contracts, then signed admission and
    sanitizer evidence.
19. SDL2 init/create/quit/destroy/present now have exact lifecycle contracts;
    quit and destroy return status, five safe wrappers use lexical FFI scopes,
    and Web UI consumes them without changing presentation cost. Continue with
    cursor, flag, and remaining property families before signed admission.
20. SDL2 cursor visibility/grab/warp now return checked status across C, Rust,
    and Simple with three lexical wrappers and unchanged SDL call counts.
    Continue with window flags/state and remaining property contracts before
    signed admission and sanitizer receipts.
21. SDL2 window flags now reserve a disjoint invalid-handle sentinel and three
    property wrappers return typed absence; quit-state operations enforce the
    owner thread and clear returns status. Continue through remaining SDL2
    properties, then implement signed provider admission and artifact-bound
    sanitizer/proof receipts before declaring this module verified.
22. Nine SDL2 window-property mutations now propagate boolean status across C,
    Rust, and Simple, and eight public wrappers use lexical FFI scopes without
    changing native-call or memory shape. Continue through the last generic
    SDL2 declarations and compatibility adapters, then bind signed provider and
    sanitizer/proof evidence before declaring SDL2 verified.
23. Eleven SDL2 display declarations now state exact sentinels/nullability;
    monitor count and monitor descriptors lift failures to typed absence with
    unchanged query and memory shape. The canonical SDL module is now 65/65
    contracted after removing the unused unchecked fullscreen ABI and typing
    error-text ownership. Next bind signed SDL artifact admission and sanitizer/
    proof receipts while continuing the wider 255-declaration SFFI inventory.
24. Winit size/scale/position reads now share the provider's scalar C ABI in
    interpreter and native lanes, use disjoint failure sentinels, and lift to
    typed absence with unchanged read/memory shape. Continue the remaining 25
    Winit declarations, then prioritize the full owned-production census
    (255 tagged-contract gaps, 347 unsafe-tag gaps, 7,584 rows missing both).
25. Winit event/window/loop release now rejects stale handles in Rust provider
    and interpreter lanes; canonical wrappers propagate lifecycle status with
    unchanged removal/call/memory shape. Continue the remaining 20 Winit raw
    declarations, duplicated app/OS declarations, and signed artifact evidence.
26. Winit staging now rejects dimension/byte overflow, binds borrowed-pointer
    extent to present dimensions, and declares raw copy ownership with the same
    single conversion allocation/copy/present shape. Continue the remaining 17
    Winit declarations and eliminate duplicate untagged app/OS bindings before
    signed provider admission and artifact-bound runtime evidence.
27. Winit fullscreen and position mutations now share integer status ABI across
    native/interpreter/Simple, invalid fullscreen reads lift to absence, and
    coordinates cannot truncate. Continue the remaining 14 event declarations,
    duplicated raw bindings, signing, and artifact-bound verification receipts.
28. Winit poll/wait now reserve negative admission failure, native wait exists
    with one bounded pump, and safe APIs expose validity while retaining exact
    event release and memory shape. Finish the remaining 12 accessor lifetime/
    type contracts, then duplicate-binding migration and signed admission.
29. Winit event accessors now use matching disjoint sentinels in native and
    interpreter lanes, validate before typed lift, and preserve one-read/one-
    release call and allocation shape; the canonical module is 30/30 contracted.
    Next migrate duplicated Winit bindings and implement signed, artifact-bound
    provider admission before claiming verified status.
30. Four duplicate Winit staging/BMP declarations now have exact lexical unsafe
    contracts; native and interpreter paths reject invalid or mismatched extents
    before allocation/pointer lift while preserving presentation call/memory
    shape. Continue the hosted-entry, compositor-input, Chromium, and game
    duplicate bindings, then implement signed provider admission.
31. Seven Chromium Winit duplicates now propagate admission/access/release
    failures with exact lexical unsafe contracts and unchanged calls/memory.
    Hosted compositor input is confirmed ABI-incompatible across lanes; add one
    generated typed snapshot/status-out thunk rather than regressing its hot path
    with extra scalar calls/locks, then migrate hosted-entry and game bindings.
32. Winit lifecycle release is standardized as boolean across Rust provider,
    interpreter, and Simple consumers. Game2D keyboard input now uses a shared
    one-call packed snapshot, preserving one dispatch/lock while removing the
    interpreter-only tuple ABI. Apply the same generated snapshot principle to
    hosted compositor mouse coordinates and remaining hosted-entry bindings.
33. The fail-closed `rt-safety-census.shs` now reports declaration/symbol totals,
    implementation languages, unsafe tags, contracts, trusted verified evidence,
    signatures, and untouched rows. Reduce the current 11,879 untouched rows by
    provider family; never lower the 12,610-row unsafe total without a trusted
    artifact-bound evidence+signature admission row.
34. The census now emits a ranked provider-family queue and a build-time ratchet
    freezes the fail-closed baseline. Migrate `rt_file`, `rt_process`, `rt_env`,
    `rt_time`, then `rt_cuda`; each improvement must reduce untouched rows or
    add exact trusted admission without adding any runtime census dependency.
