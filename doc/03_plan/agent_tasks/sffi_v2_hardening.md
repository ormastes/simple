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
65. Retain the driver scalar authority slice: remove all three
    `rt_string_len` calls, keep four env/five path/six clock calls lexical, and
    reject invalid clock samples only in the opt-in trace path. Baseline is now
    21,334 raw / 1,924 explicit / 19,410 missing calls.
66. Retain zero-forwarder lexical scopes for the remaining driver directory
    list and process capture: all 40 owner calls are now lexical, optimizer
    general patterns stay at 14, and lint has no raw-runtime warning. Baseline
    is 21,334 raw / 1,926 explicit / 19,408 missing. Next add checked list/tuple
    ABIs and migrate the six public primitive APIs; runtime signing remains a
    separate gate.
67. Retain all 20 incremental-cache file operations under direct lexical FFI
    scopes with unchanged fingerprint/write/delete call cardinality. Focused
    behavior is 7/7 plus 2/2 identity, and the baseline is 21,334 raw / 1,946
    explicit / 19,388 missing calls. Next scope or type the same owner's
    env/dir/time/PID/CLI/hash families, then address its three public primitive
    APIs. Do not claim signing from source authority.
68. Retain the OS RSA typed-result boundary: the facade must call only the
    canonical checked signature APIs, JWT must propagate `Result`, and normal
    automatic signing must perform one hosted call with Pure Simple fallback
    only after failure. Current declaration ledger is 12,019 rows / 3,172
    symbols, with zero exact-artifact signed/admitted. Re-run source checks only
    after a policy-accepted self-hosted runtime is available; do not bypass the
    production-runtime guard or restore empty-signature/boolean sentinels.
69. Retain the canonical P-256 signature owner. The common crypto facade keeps
    SPKI and fixed-width validation but must not redeclare the providers; the
    shared verifier must reject statuses outside `-1/0/1`. Ledger: 12,017
    declarations, 1,188 tagged, 10,563 untouched, and zero signed/admitted.
70. Retain the canonical Ed25519 seed-signing owner and exact 32/32/64-byte
    validation. `os.crypto.ed25519` must expose typed live-signing failure and
    must not redeclare/call `rt_ed25519_sign_seed`. Preserve the existing
    direct-plus-component diagnostic schedule; do not add provider calls,
    copies, lookups, or success-path allocations. Exact-artifact admission is
    still required before this boundary can be called verified or signed.
71. Keep `crypto_sffi` limited to implemented providers. Hash/HMAC route to
    their in-tree owners; `rt_random_hex` is the sole raw declaration and must
    remain one lexical call followed by exact entropy validation. Do not
    restore the 16 unresolved password/AES/key/PBKDF2/random-byte symbols or
    the duplicate app facade. Ledger: 11,984 rows / 3,156 symbols, 10,529
    untouched, and zero exact-artifact signed/admitted. A policy-accepted
    self-hosted runtime is still required for executable/performance evidence.
72. Keep web session-token entropy routed through canonical `random_hex` with
    exactly one provider call and bounded validation. Do not restore its local
    declaration or bypass presence/length/hex/nonzero checks. Next migrate the
    OAuth, WebSocket, credential-store, and security-type duplicates with typed
    failure propagation; never map entropy failure to zero or empty data.
73. Keep credential salt and IV entropy on canonical checked `random_hex`, one
    provider call per value, with the existing nullable failure behavior and
    JIT text re-materialization intact. Do not restore a credential-local raw
    declaration. The remaining security-types/OAuth/WebSocket duplicates need
    typed API changes because they currently fabricate usable values.
74. Keep WebSocket handshake-key and mask generation Result-bearing and routed
    through canonical checked entropy. All six browser-client call sites must
    propagate failure; never emit a zero/short mask or retry silently. Preserve
    one provider call and the existing counter-mix schedule on success.
75. Keep all three OAuth memory-model variants Result-bearing from canonical
    entropy through random integers, random strings, CSRF state, PKCE verifier,
    and mock-token creation. Never restore `?? "0"`; retain one provider draw
    per character with immediate failure and no retries. The next duplicate is
    security correlation-ID generation, which must not degrade to timestamp
    only when entropy fails.
76. Keep `rt_random_hex` single-owned: one tagged declaration and one lexical
    call in canonical `crypto_sffi`. Security correlation IDs must fail closed
    rather than degrade to timestamp-only values. Preserve one provider call
    and bounded validation; exact-artifact signature admission remains open.
77. Keep `app.io.tls_sffi` as a zero-cost compatibility re-export of the
    canonical library owner; never restore its 35 duplicate declarations or
    wrappers. Next type the canonical TLS handle/read/write/status contracts
    and migrate application modules that still import raw TLS symbols directly.
78. Keep TLS-disabled Rust runtime builds free of exported TLS stubs. Gate both
    runtime re-export layers with `runtime-tls`; a consumer requiring TLS must
    fail linkage/admission when the real provider is absent. Preserve the real
    provider hot path byte-for-byte and keep both feature configurations under
    compile checks. Next migrate raw application TLS imports to checked owners.
79. Keep web TLS reads on `rt_tls_client_read_checked`: nil is provider/contract
    failure, empty text is clean EOF, and nonempty text is data. Preserve the
    shared single-read implementation so the checked success path adds no
    descriptor, copy, retry, lookup, allocation, or dispatch. Migrate server
    reads and remaining browser/client declarations next; exact-artifact
    signing/admission remains zero and must not be inferred from this check.
80. Keep hosted and SimpleOS server reads on `rt_tls_server_read_checked`: nil
    is failure and empty text is clean EOF. The canonical friendly wrapper must
    remain Result-bearing, and the web serve loop must not redeclare raw TLS
    providers. Preserve the shared inlineable single-read path with no added
    success-path allocation, copy, lookup, descriptor, retry, or dispatch. Next
    type server accept/write/close and remove their fabricated wrapper values;
    exact-artifact admission remains a separate unmet gate.
81. Keep canonical TLS client write/read/close and server accept/write/read/
    close wrappers Result-bearing; never restore zero, false, empty text, or a
    dummy resource as safe-wrapper failure. Preserve semantic boolean close
    status and one-call/one-branch success paths. Raw accept/write/read/close
    declarations must retain minimal `unsafe(ffi)` tags. Next type connect,
    server create/shutdown, certificate, and configuration families; signed
    exact-artifact admission remains zero.
82. Keep TLS connect/SNI connect/server-create wrappers Result-bearing and
    server shutdown `Result<()>`; never restore invalid resource objects or an
    ambiguous safe boolean. Preserve provider-native negative handles and
    semantic boolean status, with one call and one branch on success. Next
    remove fabricated certificate/configuration handles and truthful-status
    stubs; exact-artifact admission remains zero.
83. Do not restore the ten unimplemented TLS client/server configuration
    symbols. A future configuration API must own real rustls state and prove
    handle lifetime, mutation, ALPN, trust-root, verification-mode, and release
    contracts before registry admission. The current removal adds no memory or
    dispatch overhead. Next remove or implement the fabricated certificate and
    connection-info providers; signed exact-artifact admission remains zero.
84. Do not restore the ten fabricated TLS certificate/peer/self-sign/hash
    symbols or their atomic fake-handle generator. Peer certificate metadata
    remains explicitly optional until a real owned certificate representation,
    parser, validation policy, and destructor are implemented. Next make
    protocol/cipher/ALPN/handshake connection info truthful and typed; signed
    exact-artifact admission remains zero.
85. Keep TLS protocol/cipher/ALPN/handshake metadata nullable and truthful:
    invalid/stale/incomplete is nil, valid no-ALPN is empty text, and handshake
    payload remains bool. Cipher names must use static literals rather than
    formatting allocations. Safe wrappers stay Result-bearing and browser/
    interpreter paths must handle absence. Next consolidate browser TLS raw
    declarations and checked reads/writes; signed admission remains zero.
86. Keep browser TLS routed through the canonical owner with Result-bearing
    connect/read/write/close. Address connect, write timeout, and checked read
    timeout must call their real bounded provider exactly once; never restore
    ignored-timeout duplicate branches or ambiguous legacy reads. Next remove
    remaining legacy client read exports once all callers migrate; exact signed
    artifact admission remains zero.
87. Do not restore ambiguous `rt_tls_client_read`,
    `rt_tls_client_read_timeout`, or `rt_tls_server_read`. All lanes must expose
    checked nullable reads only; nil is failure and empty text is EOF. SimpleOS
    must retain fail-closed checked/timeout symbols for sealed linkage. Next
    audit the remaining 19 canonical TLS declarations and eliminate duplicate
    noncanonical callers; signed artifact admission remains zero.
88. Keep `app.io.graphics2d_sffi` a zero-cost re-export of the canonical
    library owner. Never restore its 49 declarations or negative-handle
    `handle != 0` semantics. Next type/tag the canonical Lyon contracts and
    replace dummy resource/zero/empty wrapper failures with Results where the
    API is fallible; exact signed artifact admission remains zero.
89. Keep all 49 canonical Lyon declarations explicitly tagged `unsafe(ffi)`;
    the tags document raw ownership but do not promote the wrappers to safe or
    verified. Migrate resource construction, tuple/count access, and array
    extraction to typed failure without extra provider calls or copies, then
    bind the exact provider artifact to signed admission evidence.
90. Keep all 49 canonical SIMD declarations explicitly tagged `unsafe(ffi)`
    without adding generic dispatch or wrapper allocations. Next bind each
    target-specific vector signature and provider implementation to an ABI
    fingerprint and exact signed artifact; retain direct typed calls on the hot
    path and keep feature/profile values semantically typed.
91. Keep `app.io.rapier2d_sffi` a zero-cost re-export of the canonical owner;
    never restore its 48 declarations or `handle != 0` resource validation.
    Tag and type the canonical Rapier2D boundary next, preserving one direct
    provider call per operation and avoiding copies or generic dispatch.
92. Keep all 48 canonical Rapier2D declarations explicitly tagged
    `unsafe(ffi)`. Migrate dummy resource and ambiguous tuple/scalar failures to
    typed `Result` APIs in a separately reviewed compatibility change, with one
    direct provider call and no added array copies; exact signed admission is
    still required.
93. Keep unadmitted GPU-session and Engine2D Metal pseudo providers scoped to
    `rt_gpu_session_metal_*` and `rt_engine2d_metal_session_*`; never reuse a
    canonical `rt_metal_*` identity with a different signature. Either provide
    and admit the exact scoped ABI or remove the unsupported facade. Continue
    canonical Metal tagging without adding hot-path adapters.
94. Keep the canonical Metal owner at 40 explicitly tagged raw declarations
    until a reviewed provider change alters the inventory. Never restore the
    always-zero sampler/swapchain/present facade; implement and admit a real
    provider contract before exposing those APIs. Preserve direct batched GPU
    submission and existing buffer-copy counts.
95. Treat the refreshed authoritative baseline as 11,819 `rt_*` declaration
    rows / 3,138 symbols, 1,410 unsafe-tagged, 10,151 untouched, and zero signed
    admissions. Continue from the largest owned production untouched owner;
    never infer semantic verification from an unsafe tag alone.
96. Keep `std.nogc_sync_mut.ffi.debug` a zero-cost re-export of canonical
    `std.nogc_sync_mut.sffi.debug`; never restore its 43 duplicate declarations.
    Tag and classify the canonical ptrace/DWARF contracts next, preserving
    direct debug calls and exact buffer behavior.
97. Keep all 43 canonical debug declarations explicitly tagged `unsafe(ffi)`.
    Before publishing safe ptrace/DWARF APIs, type status and not-found results,
    prove returned collection ownership, enforce platform/debug capability
    policy, and bind the exact provider artifact without adding debug syscalls
    or process-memory copies.
98. Keep `std.nogc_sync_mut.ffi.cli` a provider-free compatibility facade and
    retain `cli_run_ffi_gen` / `cli_ffi_gen` only as aliases to the implemented
    canonical SFFI generator. Keep all 40 canonical CLI declarations explicitly
    tagged; never restore the unimplemented `rt_cli_run_ffi_gen` symbol.
99. Keep all 40 canonical GLFW declarations explicitly tagged `unsafe(ffi)`.
    Preserve one presentation call and the existing pixel storage: enforce
    width/height/count overflow and pointer-lifetime contracts at the boundary
    without adding frame copies, per-frame lookup, or generic dispatch.
100. Keep all 41 compiler minimal-runtime declarations explicitly tagged
     `unsafe(ffi)`. Validate the string out-length ABI and owned/borrowed pointer
     distinctions before safe publication; preserve existing allocation,
     clone/free, environment, and filesystem call counts.
101. Keep all 39 canonical audio declarations explicitly tagged `unsafe(ffi)`.
     Enforce PCM pointer/count/channel/frame extent and handle-generation
     contracts at the boundary without sample copies, callback indirection, or
     extra queue/provider calls; exact signed admission remains required.
102. Keep all 37 bootstrap allocation/collection/string declarations explicitly
     tagged `unsafe(ffi)`. Replace dynamic `Any` and untyped pop/get/lookup
     sentinels with canonical typed ABI contracts without adding allocations,
     collection scans, string copies, or generic hot-path dispatch.
103. Keep all 36 simple-core process/time/panic declarations explicitly tagged
     `unsafe(ffi)`. Enforce pointer extents, signal-handler validity, post-fork
     restrictions, and owned argument-value transfer without extra allocation,
     process calls, or copies; bind exact libc/runtime identity before admission.
104. Keep all 35 simple-core string/stdio declarations explicitly tagged
     `unsafe(ffi)`. Enforce memory and I/O extents, parsing end-pointer validity,
     array item-pointer lifetime, and enum payload borrowing without extra
     scans, allocations, copies, syscalls, or string-registry work.
105. Keep all 34 simple-core filesystem declarations explicitly tagged
     `unsafe(ffi)`. Enforce partial-I/O, stdio element extents, mmap sentinels
     and lifetimes, directory-entry borrowing, and path validity without extra
     path copies, directory scans, allocations, or syscalls.
106. Keep hosted entry free of local `rt_winit_*` declarations and preserve the
     canonical boolean fullscreen/release contracts. Keep all 35 Winit owner
     declarations tagged and the four irreducible hosted time/env/args externs
     tagged, without adding event polls, wrappers, copies, or render work.
107. Keep all 48 TLS 1.3 context declarations explicitly tagged `unsafe(ffi)`.
     Replace ambiguous empty-array and numeric parser/status/equality contracts
     with typed results without extra hashes, HKDF/HMAC operations, record
     parses, transport calls, allocations, or byte-array copies.
108. Use the refreshed authoritative baseline: 11,713 `rt_*` declaration rows /
     3,137 symbols, 1,737 unsafe-tagged, 9,720 untouched, and zero signed
     admissions. Continue with bootstrap `infra/file_io.spl` (33 untouched
     rows), preserving its filesystem call and buffer-copy counts.
109. Keep all 35 bootstrap file-I/O declarations explicitly tagged
     `unsafe(ffi)`. Preserve optional reads and migrate ambiguous non-optional
     empty text/list returns to typed errors without extra preflight calls,
     recursive scans, path normalization, allocations, or buffer copies.
110. Keep `std.nogc_sync_mut.ffi.runtime` a zero-cost re-export of canonical
     `std.nogc_sync_mut.sffi.runtime`; never restore its 32 duplicate
     declarations. Tag the canonical GC/runtime-value contracts without adding
     allocation, collection, clone/free, or dispatch overhead.
111. Keep all 32 canonical runtime declarations explicitly tagged
     `unsafe(ffi)`. Validate allocation/projection failures, string out-length,
     and owned result lifetimes before safe publication without extra GC work,
     allocations, clones, frees, arithmetic calls, copies, or dispatch.
112. Keep all 39 canonical system declarations explicitly tagged `unsafe(ffi)`.
     Preserve nullable environment lookup and direct process/clock operations;
     migrate ambiguous empty text and timestamp/host sentinels to typed results
     without extra lookups, processes, captures, clock calls, parses, or sleeps.
113. Keep all 34 canonical I/O declarations explicitly tagged `unsafe(ffi)`.
     Migrate ambiguous empty text/array/hash and lock/mmap sentinels to typed
     results without extra filesystem calls, hash passes, lock attempts, mmap
     operations, recursive scans, path transforms, allocations, or copies.
114. Keep `std.nogc_sync_mut.ffi.ast` a zero-cost re-export of the canonical
     `std.nogc_sync_mut.sffi.ast` owner and keep all 29 owner declarations
     explicitly tagged `unsafe(ffi)`. Validate opaque-handle generation,
     kind/index access, owned text, and release contracts without extra registry
     lookups, AST walks, allocations, string copies, branches, or dispatch.
115. Keep all 29 application-interpreter AST declarations explicitly tagged
     `unsafe(ffi)` until its raw-name import surface can be migrated to the
     canonical owner. Preserve boolean results and direct opaque-handle calls;
     do not add registry lookups, AST walks, allocations, copies, or dispatch.
116. Keep all 27 SQLite declarations in each legacy library/application facade
     explicitly tagged `unsafe(ffi)` until a single generated owner replaces
     them. Introduce status/out v2 across native C, Rust interpreter, and Simple
     atomically: distinguish row/done/error, null/value/error, and valid-zero/
     failure without extra SQL calls, statement steps, column reads, string
     copies, allocations, registry lookups, or generic dispatch.
117. Retain the native SQLite O(1) heap-tag guards and reject `close(nil)` as
     failure. Keep transaction control on static C strings so begin/commit/
     rollback add no temporary runtime-string allocation or copy. Full stale/
     wrong-kind handle safety still requires generation-checked typed handles.
118. Keep all 26 HTTP/WebSocket declarations in each legacy library/application
     facade explicitly tagged `unsafe(ffi)`. Preserve direct provider calls and
     boolean results. Generate one authoritative owner and typed transport/
     protocol errors without extra DNS queries, connections, requests, reads,
     copies, allocations, locks, handle lookups, or dispatch.
119. Keep all 25 unbacked FTP declarations explicitly tagged `unsafe(ffi)` and
     keep storage selection fail-closed. Do not add weak/fabricated providers.
     Any future FTP/FTPS provider requires typed ownership/status contracts,
     TLS policy, exact signed admission, and no extra network/file operations,
     copies, allocations, lookups, locks, or generic dispatch on the hot path.
120. Keep all 24 simple-core array allocator/pointer/archive externs explicitly
     tagged `unsafe(ffi)` with `raw_ptr` where applicable. Retain allocation-
     failure cleanup and constant-time capacity/concatenation overflow guards;
     add no array traversal, copy, allocation, registry lookup, or dispatch.
121. Keep the 26 bootstrap synchronization declarations ABI-aligned and
     explicitly tagged `unsafe(ffi)`. Do not restore value-less mutex/RwLock
     constructors, one-argument mutex unlock, integer TLS values, numeric Once
     booleans, or no-op RwLock unlock shims. Replace CondVar/Once provider stubs
     with real atomic guard/callback contracts without extra steady-state locks,
     allocations, registry lookups, sleeps, spins, or dispatch.
122. Keep all 25 bootstrap shell filesystem/environment/process/path externs
     explicitly tagged `unsafe(ffi)`. Preserve missing versus empty environment
     values with one lookup. Migrate ambiguous file/list/path results to typed
     errors without extra filesystem scans, process launches, captures,
     allocations, copies, environment reads, or generic dispatch.
123. Keep all 24 bootstrap math `f32` declarations explicitly unsafe until
     generated `_f32` symbols/thunks separate them from canonical `f64`
     providers. Preserve the public `f32` API and direct hardware/libm call
     shape; add no heap allocation, boxing, lookup, conversion loop, or generic
     dispatch. Bind both typed symbol sets into the ABI registry.
124. Keep all 24 unbacked compression/archive declarations explicitly tagged
     `unsafe(ffi)`. Do not publish the facade as verified while binary payloads
     use `text`, failures are ambiguous, handles lack typed ownership, or
     extraction limits/path policy are unproved. A future provider must use
     byte spans, typed status/handles, bounded decompression, safe extraction,
     and exact signed admission without extra hot-path lookups, copies,
     allocations, locks, or generic dispatch.
125. Keep all 23 unbacked SSH/SFTP declarations explicitly tagged
     `unsafe(ffi)` and keep compatibility families delegated to the canonical
     no-GC owner. Do not add weak providers. A future typed provider must bind
     host-key policy, credentials, handle generations, partial I/O, bounded
     command/channel output, remote path semantics, and typed errors to exact
     signed admission without extra network/file operations, allocations,
     copies, lookups, locks, or generic dispatch on the hot path.
126. Keep all 38 process declarations across the canonical library and
     application closure owners explicitly tagged and lexically scoped. Do not
     add weak browser-sandbox providers. Generate one authoritative contract
     for nullable file reads and fallible stderr/flush status, then migrate the
     duplicate declarations together. Preserve one provider call per operation
     and add no polling, filesystem scan, launch, allocation, copy, lookup,
     lock, branch, or generic dispatch beyond contract-required status checks.
127. Keep all 37 shared `io_runtime` declarations explicitly tagged and
     lexically scoped. Preserve optional raw byte/list/platform results with
     one-call public fallbacks. Generate canonical typed exit thunks for Rust
     `i32`/never and simple-core `i64`/return differences, and replace shell,
     destructive directory, hash, clock, and array ambiguity with typed
     contracts. Add no filesystem operation, traversal, launch, allocation,
     copy, lookup, lock, or generic dispatch beyond required status checks.
128. Keep all 20 canonical atomic declarations explicitly tagged and
     lexically scoped, and keep GC/no-GC async families as zero-cost facades.
     Retain one-call Boolean CAS/and/or/not primitives; never
     restore multi-call load/swap/store compositions. Replace hosted global
     mutex/hash-map handles with typed generation-checked direct slots and
     honor requested memory ordering, with a complete pure-Simple bootstrap
     contract. Add no per-call allocation, copy, retry, lookup, lock, generic
     dispatch, or stronger fence beyond the selected ordering.
129. Keep all 21 fast in-memory database declarations explicitly tagged and
     lexically scoped. Retain PureDatabase as the default general embedded
     database; this specialized C accelerator remains unsafe until its global
     registry is synchronized, handles are generation checked, and every
     sentinel/status is typed. Never reinterpret integer batch values as text
     pointers. Preserve O(1) indexed operations and add no per-call hash,
     signature check, registry lookup beyond the existing table/index access,
     allocation, copy, lock, or generic dispatch. Exact signed admission and
     cross-lane contract equivalence remain required before safe publication.
130. Keep all 24 canonical oneAPI declarations explicitly tagged and all raw
     calls lexically scoped. The current native and interpreter lanes expose
     only 14 fixed unavailable stubs; the other 10 declarations are unbacked.
     Do not treat unavailable sentinels as a verified GPU provider and do not
     fabricate successful cleanup/wait for invalid handles. Replace both C
     stub copies and the handwritten Rust dispatcher with one generated typed
     registry only when a real SYCL/Level Zero provider exists. Bind device,
     allocation, queue, module, kernel, span, and error contracts to exact
     signed admission without adding per-launch hashing, signing, discovery,
     lookup, allocation, copy, lock, or generic dispatch.
131. Keep all 23 Engine2D CUDA declarations explicitly tagged and every static
     call lexically scoped. Keep the facade class unsafe until handles, spans,
     dynamic symbols, and ownership are generated typed contracts. Never use
     generic all-integer dynamic calls for CUDA out-parameter APIs; availability
     may call `cuInit(0)` directly, while device count, context creation, and
     allocation use typed static thunks until typed dynamic thunks exist. Keep
     the six unbacked shutdown/argument-pack/pixel-helper symbols visible and
     fail closed. Preserve direct launch/copy paths with constant-time extent
     guards and no per-call hashing, signing, discovery, extra allocation,
     copy, lock, lookup, or generic dispatch.
133. Keep `CudaDynFfi` reduced to nine exact, explicitly unsafe static CUDA
     declarations. Never restore its unbacked Engine2D helpers, legacy shutdown,
     old aliases, or function-handle signature under the canonical module/name
     `rt_cuda_launch_kernel` identity. Static function-handle launch must fail
     closed until a uniquely named typed provider exists; dynamic launch may
     retain one direct `cuLaunchKernel` call. Continue using typed static thunks
     for CUDA out-parameter operations. Add no per-launch allocation, copy,
     hash, signature check, discovery, lock, lookup, or adapter dispatch.
134. Keep all 23 ROCm I/O declarations explicitly tagged and raw calls
     lexically scoped. Preserve the real Linux runtime provider's direct HIP
     calls and existing array-layout staging; do not treat the interpreter's
     fixed unavailable simulation as cross-lane verification. Retain nullable
     managed-text lifting, allocation/copy extent checks, launch geometry and
     overflow guards, and error-path release. Do not add successful-path
     provider calls, staging allocations, copies, dynamic lookups, locks,
     hashes, signature checks, or generic dispatch. Generated typed contracts,
     handle generations, and exact signed provider admission remain required.
