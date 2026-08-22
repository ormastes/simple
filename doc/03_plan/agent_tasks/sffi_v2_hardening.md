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
    signatures, and untouched rows. Reduce the current 11,899 untouched rows by
    provider family; never lower the 12,650-row unsafe total without a trusted
    artifact-bound evidence+signature admission row.
34. The census now emits a ranked provider-family queue and a build-time ratchet
    freezes the fail-closed baseline. Migrate `rt_file`, `rt_process`, `rt_env`,
    `rt_time`, then `rt_cuda`; each improvement must reduce untouched rows or
    add exact trusted admission without adding any runtime census dependency.
35. Rust-seed HIR now retains lexical `unsafe(ffi)` authority through a checked
    pre-MIR pass and denies unscoped extern calls in critical/verified profiles,
    with a process-cached policy lookup and unchanged target code. Extend the
    same seed pass to raw pointers/inline assembly, then migrate the ranked
    `rt_time` provider declarations and wrappers without adding call overhead.
36. The canonical three `rt_time` clocks now reserve and propagate `-1`, lift
    failure in Rust/Simple, and have exact minimal lexical FFI scopes. Failure
    sabotage, epoch parity, lint, syntax, one-call shape, and census ratchet pass.
    Continue the remaining 367 `rt_time` declaration rows and timestamp
    arithmetic contracts, then attach exact signed provider artifact evidence.
37. Progress init/reset now use boolean ABI across C, Rust, interpreter, and
    Simple; elapsed/seconds failures use a negative sentinel and thread-local
    state removes parallel races with no heap or per-call mutex. Seven rows
    advance the ratchet. Continue duplicate clock declarations and timestamp
    arithmetic contracts before signed artifact admission.
38. The canonical process facade now isolates nine raw contracts in minimal
    lexical FFI wrappers. Rust runtime/interpreter child publication kills and
    reaps on registry failure, malformed arguments fail before spawn, and the
    successful path retains one lock+insert with no new allocation. Continue
    the remaining 1,035 `rt_process` rows, then bind exact signed provider
    evidence before any process row can leave the unsafe class.
39. The canonical library process owner now isolates twelve more raw contracts
    in allocation-free lexical FFI wrappers. Its live relay uses checked offset
    reads instead of quadratic whole-file polling, with focused correctness and
    static hot-path guards. Continue the remaining 1,023 `rt_process` rows and
    repair the module's existing primitive-API lint debt; signed artifact-bound
    admission is still required before any SFFI row is classified verified.
40. `std.ffi.system` is now a zero-runtime-cost export facade over the canonical
    SFFI system owner, removing 40 duplicate declarations while preserving all
    45 public APIs. Eight canonical process/native hooks have unique minimal FFI
    scopes and explicit failure contracts. Continue the remaining 1,011
    untouched `rt_process` rows, then implement exact signed artifact admission;
    declarations remain unsafe until both evidence checks succeed.
41. Remove the eight-hook dead seed process declaration surface and keep it
    absent with the owner audit. Five hot `io_runtime` process hooks now have
    explicit contracts and minimal lexical scopes; owner-alias consolidation is
    deferred by a documented JIT deoptimization bug, not silently accepted.
    Continue the remaining 999 untouched process rows and fix alias lowering
    before removing these direct declarations. Signed admission remains zero.
42. Remove the four C-owned editor DAP convenience symbols and route spawn,
    framing, bounded incremental parsing, and event polling through the existing
    Pure Simple DAP client. Preserve one checked nonblocking read per poll,
    cap each client at 64 KiB, drain queued messages linearly, and prevent
    request-sequence reuse after checked startup. Next migrate raw PID identity to
    generation-bearing handles and attach exact signed provider evidence.
43. Repair the stage4 process-provider source-introspection spec so it selects
    the intended strict-link block, and migrate the module's 25 public primitive
    parameters to semantic wrappers. Keep the direct 15-symbol DAP/process
    closure audit release-blocking until that full spec and lint are green.
44. Rebuild and deploy the Pure Simple runtime with
    `rt_process_is_alive_checked` registered, then rerun the real editor DAP
    command smoke. Do not fall back to the Rust seed; retain the measured
    9.55-second/260,968-KiB failed smoke receipt until the rebuilt lane passes.
45. Fix native-build worker orchestration so `--threads 8` shares one closure,
    load, and parse phase instead of evaluating the 1,865-file manifest eight
    times; also restore the missing `runtime_file_rename` JIT registration.
    Resume the preserved `build/bootstrap/native_cache` only after those owners
    are fixed, then produce and smoke the Pure Simple candidate once.
46. Fix self-hosted entry-closure HIR origin resolution for editor semantic
    types. The bounded 173-file, single-worker DAP smoke build parsed in
    656.85 seconds but produced 44 entry-module unresolved-type errors and 121
    accumulated errors by 730.82 seconds. Preserve the cache, add a focused
    closure regression, and rerun this smoke only once after the owner fix.
47. Verify the consolidated module-surface identity on the preserved editor-DAP
    cache. The second build parsed in 892.92 seconds and proved the surface
    layer still had a private normalizer; that duplicate is now removed in
    favor of `module_logical_name_from_path`. Run the cached smoke once in a
    fresh session because this session reached its three-cycle cap.
48. Repair physical-path lookup for resolver-transparent numbered module
    surfaces and add the missing `MdMotionResult` owner to the focused closure.
    The closure now correctly contains 178 files and the former 44 editor-type
    failures are gone, but HIR reports `missing importing module surface` for
    `src/std/editor/00.common/*.spl`. Pin physical and logical lookup together
    before another cached end-to-end build.
49. Add explicit type/function imports to the editor view modules revealed by
    the now-correct closure (`EditorDocumentId`, `EditorBuffer`, and
    `render_block_line_span`). The entry and numbered common owners now lower
    cleanly; do not rerun the full build until focused view-module coverage is
    green. Ensure build cancellation terminates worker descendants, since the
    prior launcher-only Ctrl-C left eleven cache writers and about 39 GiB RSS.
50. Keep the preview marker linear: retain the Pure Simple `StringBuilder`
    implementation and its focused lint gate. On a fresh verification turn,
    run one cached single-worker editor-DAP native build, measure its smoke
    timing and peak RSS if it produces an artifact, and do not publish an
    end-to-end verified claim before that receipt exists.
51. Verify the canonical process-owner imports in one fresh cached build. The
    last bounded run parsed in 94.27 seconds and reached HIR, but `std.io`
    resolved without its process exports in entry-closure mode. DAP and LSP now
    import `std.nogc_sync_mut.io.process_ops` directly; do not add a runtime
    adapter, dynamic dispatch, or per-call allocation to solve this compile-time
    ownership issue.
52. Retain the linear LSP framing/JSON parser changes: direct integer parsing,
    `StringBuilder` text extraction, and loop-length hoisting. Add or reuse real
    framing/parser correctness examples before claiming the concurrent LSP
    migration verified; do not restore concatenation-based parser loops.
53. Verify the corrected `md_vim_*` owner in one fresh cached build. These nine
    typed motion functions belong to `std.editor.view.md_editing`, not the
    similarly named builtin motion module. The 153-source closure and the
    explicit commands/preview/process owners already lower cleanly; retain that
    14.5% closure reduction and do not reintroduce wildcard facade imports.
54. Repair the MIR closure after the now-green 153/153 HIR phase. Start from
    the captured cycle-three diagnostics (`EditSession`, office sheet types,
    window event constants/types, SIMD `Vec8i`, and unresolved string methods).
    Keep `SIMPLE_NO_STUB_FALLBACK=1` release-blocking: any unresolved method
    lowered to constant zero is a fabricated value and must reject admission.
55. Preserve the canonical typed piped-process lifecycle results for spawn,
    stdin write, and close. Production DAP must consume these `Result` APIs,
    while compatibility boolean/integer functions remain only for unmigrated
    callers. Keep the one-provider-call hot path and add no per-call lookup,
    retry, allocation, or copy. Next add generation-bearing handles and migrate
    remaining direct `rt_process_*` declarations by owner rather than tagging
    duplicate declarations mechanically.
56. Use the current 12,065-row census as the next ratchet baseline: 353
    unsafe-minimized, 11,712 unsafe-unminimized, 10,987 untouched, and zero
    verified/signed. Prioritize `rt_file`, `rt_process`, `rt_env`, `rt_time`,
    and `rt_cuda`; do not claim source tags, fixture signatures, or synthetic
    receipts as production verification.
57. Close the focused lint blocker in the canonical process owner by replacing
    bare public PID/status primitives with semantic handle/status types and by
    routing its remaining file, stream, and browser intrinsics through their
    owning facades. Preserve raw ABI scalars inside the minimal unsafe wrapper;
    do not add conversion allocation or extra provider dispatch.
58. Ratchet the live call-authority census alongside declarations. Current
    baseline: 21,371 raw calls, 12,903 production calls, 1,885 explicitly
    authorized, and 19,486 missing authority after completing Torch call authority. Use the per-symbol/family/scope
    reports to prioritize real production exposure, and keep report generation
    to one source scan plus linear aggregations.
59. Keep all 1,027 production `rt_torch` calls under minimal lexical FFI
    scopes or checked semantic wrappers. Do not merely reclassify the census.
    Preserve the current number of provider calls and CUDA synchronization
    points, and do not add per-call symbol lookup, availability probing,
    allocation, handle copies, or device transfers.
60. Keep `scripts/audit/baselines/sffi-call-authority-v1.tsv` monotonic. Missing
    authority may decrease but must not rise above 19,486. Update the baseline
    only in the same reviewed change that proves the corresponding raw calls
    gained minimal lexical authority or were removed; never relax it to absorb
    an unrelated regression.
61. Retain the completed compiler CAS semantic-owner migration: the sabotage
    gate passes 1+3 cases, the seed-only behavior spec passes 12/12, and the
    census is 21,337 raw / 19,451 missing-authority calls. Preserve the unique
    one-call `file_move_cross_device` owner and do not restore the ambiguous
    `file_rename` alias. This is unsafe minimization, not signed admission.
62. Split the legacy `io_runtime` aggregate into lint-recognized canonical
    provider owners, replacing its 39 primitive-API errors and raw-runtime
    warnings with typed status/`Result` boundaries. Preserve one provider call,
    add no success-path error allocation, and bind exact runtime artifact
    signature/evidence before classifying any file/env/time family verified.
63. Retain all 23 driver source-loading file calls under minimal lexical FFI
    authority and keep candidate path construction hoisted. Census baseline is
    now 21,337 raw / 1,909 explicit / 19,428 missing calls. Fix the expression-
    form unsafe parser gap before replacing the compatible statement form.
64. Retain `_driver_entry_import_dirname`'s verified linear last-separator
    slice: 6/6 behavior examples cover leaf/root/relative/trailing/repeated
    separators, optimizer opportunities fall 246 to 243, and `COLL006` is gone.
    Next migrate the same file's env/time/path/dir/process calls and six public
    primitive APIs without adding lookup, allocation, or provider dispatch.
    Signed runtime admission remains a separate gate.
