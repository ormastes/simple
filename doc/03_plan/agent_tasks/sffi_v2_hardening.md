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
42. Audit the duplicated interpreter-debug facades against the Rust runtime
    before consolidating them: retain only used raw declarations, require
    lexical `unsafe(ffi)`, and convert the provider's negative status returns
    into `Result.Err` rather than a fabricated success. Keep the two facades
    byte-equivalent apart from coordinator ownership, and protect that rule with
    a static audit. This is a cold debugger-control boundary: do not introduce
    call-time registry work, allocations, copies, or loops. The focused source
    check and both authority audits pass under the bootstrap seed, while signed
    provider admission remains zero. Next, migrate another ranked provider
    family or implement exact artifact-bound admission; do not call the global
    SFFI inventory safe or verified.
43. Contain the canonical advanced scalar-math facade without replacing its
    fixed-`f64` provider with a slower fallback. Require `unsafe(ffi)` on its
    twelve declarations and lexical scopes on all thirteen calls, including the
    round helper. Preserve NaN/infinity as valid IEEE-754 values and retain the
    direct call shape; prohibit call-time admission, lookup, hashing, generic
    dispatch, allocation, and copying. The static authority audit, source
    check, 13-case math spec, and optimizer review pass under the bootstrap
    seed. Signed admission remains zero; continue with a provider that has a
    complete ABI/evidence path rather than labeling scalar containment verified.
44. Keep raw interpreter error handles in one canonical SFFI owner. Remove
    duplicate compatibility declarations, annotate all remaining handle
    operations `unsafe(ffi)`, and make aliases call the scoped wrapper rather
    than the raw symbol. Preserve the direct one-call path and reject fabricated
    handle/message fallbacks. Static owner audit, source check, and optimizer
    review pass; unsigned, interpreter-owned handle lifetime remains an explicit
    unsafe limitation until multi-lane provider/evidence admission exists.
45. Harden the counterpart dynamic-provider ABI owner: tag and lexically scope
    its nine raw shim calls, remove missing-foreign-value-to-empty-text
    coercions, and retain its existing status/manifest fail-closed behavior.
    Preserve direct calls with no call-time admission work. Static authority
    and source checks pass; runtime proof is blocked by a stale bootstrap
    artifact missing registered `rt_counterpart_*` handlers. Do not claim the
    provider signed or globally verified until deployed-artifact parity and
    artifact-bound evidence are repaired.
46. Keep SFFI evidence admission cryptographically precise: trust-store keys
    scoped to a provider must be inspected as Ed25519 before raw signature
    verification, so a trusted RSA/ECDSA key cannot silently change the stated
    signature scheme. The dedicated contract fixture must admit a valid
    Ed25519 provider and reject a trusted RSA key. This check is load-time-only
    and must not add call-time work. It strengthens the future admission gate;
    it does not create a provider artifact job or change the zero signed count.
47. Contain the direct AES-XTS runtime ABI without replacing its fixed-size
    native block path. Keep the three raw declarations and all sixteen uses
    lexical `unsafe(ffi)`, require bounds/round preconditions in their owner,
    and guard the absence of per-call admission or generic dispatch. Preserve
    direct allocation and AES call shape; the pending interpreter `u8` lifting
    bug blocks XTS KAT evidence, and artifact-bound admission remains zero.
48. Repair channel send-result propagation across Simple, interpreter, and
    native provider paths. Preserve the `1` admitted / `0` rejected ABI instead
    of manufacturing `true` after a rejected send; tag six raw declarations
    and scope thirteen calls lexically. Remove the redundant closed-state query
    from `try_send`, add no allocation/copy/lookup work, and keep unsigned
    channel ownership explicitly unsafe until exact artifact evidence exists.
49. Keep the MIR actor runtime bridge ABI-exact: `rt_actor_spawn` passes its
    required context and `rt_actor_recv` has no invented timeout parameter.
    Keep mutex unlock and rwlock store as `i64` status contracts, with lexical
    FFI scopes and a static synchronization authority guard. Do not extend this
    narrow repair into `actor_hooks.spl`: its public scheduler semantics are
    incompatible with the runtime ABI and require a pure-Simple owner migration
    or generated contract. Signed provider admission remains zero.
50. Before any global-safe claim, obtain an authorized Ed25519 trust anchor and
    an exact provider job containing artifact, source, build-input, compiler,
    ABI-registry, and verification-report identities. Until then, continue
    ranked boundary containment but report every raw provider as unsigned and
    not globally verified; a no-verify convenience switch must not alter this
    classification.
51. Keep the retired legacy actor-hook facade free of `rt_actor_*` declarations
    and calls. Its former `Any`/actor-id ABI is incompatible with the runtime;
    stale compatibility callers must fail closed with
    `E-SFFI-ACTOR-LEGACY-ABI` and migrate to scheduler-owned pure-Simple actors.
    The static guard is a ratchet only; it does not count as provider signing.
52. Keep ambiguous raw runtime-owned I/O text/hash facades explicitly unsafe,
    but require a smallest lexical FFI scope for every direct raw call. Do not
    coerce failure to empty text or add call-time validation work; migrate the
    ABI to nullable/status-out before declaring these facade results safe.
53. Keep compiler CAS raw filesystem/process/time calls behind six private
    always-inline lexical owners. Preserve its atomic-rename and corruption
    semantics while preventing direct-call spread. Treat the optimizer's 70
    reported module opportunities as a separate measured-performance task; do
    not fold unmeasured collection/loop rewrites into SFFI containment.
54. Keep fast-GC's twelve raw directory/filesystem/time contracts behind
    private always-inline lexical owners. Preserve nullable-size/list/walk and
    atomic-trash behavior. Before changing its existing selection sweep, add a
    bounded candidate benchmark; the current source-text lease test failure
    (`variable dir not found`) is a separate compiler/test defect and cannot be
    recorded as a fast-GC pass.
55. Keep cache admission's filesystem/directory raw calls behind four inline
    lexical owners and use the canonical nullable pin-read facade. Do not call
    the current `nil`-to-empty-pins policy verified: migrate it to a distinct
    missing-versus-unreadable status before mission-critical cache admission.
    Measure the recorded optimizer candidates independently.
56. Keep mark-sweep's seven raw filesystem/directory/process/time calls behind
    inline lexical owners and route text reads through the canonical nullable
    facade. Do not infer safe pin/manifest semantics from `nil`-to-empty
    normalization; define typed unreadable-input outcomes before marking the
    cache GC verified or signed.
57. Retain the cache unreadable-input fail-closed rule: existing pins reads
    fail with `E-SFFI-CACHE-PINS-READ` and existing mark-sweep manifest reads
    fail with `E-SFFI-CACHE-MANIFEST-READ`; normal absent pins remain empty.
    Do not reintroduce `file_read_nullable(...) ?? ""` on either path.
58. Keep cache lease's eight raw contracts behind inline lexical owners.
    Unreadable existing leases fail closed for query paths and remain retained
    by reclaim; do not silently convert them to empty text or delete them.
59. Continue from the 2026-08-27 authority census (14,064 missing, 2,298
    lexical, 1,625 function-wide scopes). Prioritize SSH session and Torch
    dynamic operations only after provider-specific ABI/ownership contracts are
    frozen; do not bulk-tag their large surfaces or claim source census as
    signed verification.
60. Keep all 61 calls in the dynamic Torch facade inside minimal lexical
    `unsafe(ffi)` expressions. The availability wrapper is always-inline and
    each typed constructor/result wrapper retains one direct provider call,
    nonpositive-handle rejection, and no explicit allocation, copy, lookup,
    lock, or loop. This is containment only: legacy fixed-dimension ABI,
    ownership, provider artifact identity, and verification receipts remain
    incomplete, so the provider remains unsafe and unsigned.
61. The refreshed live-backing source census has 11,113 declaration rows,
    3,123 unsafe-tagged rows, 922 unsafe rows with a documented contract, and
    7,750 untouched rows. It has zero verified-and-signed rows. Use these
    scoped census values for progress reporting; they are not a substitute for
    ABI, ownership, artifact, signature, or semantic verification evidence.
62. Keep the legacy SSH/SFTP client facade explicitly unsafe until it has a
    real provider. Its 23 declared raw calls are unbacked and therefore remain
    public unsafe wrappers, but each direct call must have a smallest lexical
    `unsafe(ffi)` scope. Do not turn its ambiguous text, tuple, or boolean
    values into safe APIs; no allocation, lookup, lock, or per-call admission
    work is permitted while the facade is retained for compatibility.
63. Keep the syscall-backed clock/progress owner exact: all nine declarations
    are `unsafe(ffi)`, the six executed raw calls are lexical, and native clock
    failures retain the documented negative sentinel. Do not add a second clock
    read, allocation, lock, lookup, or retry to progress init/elapsed paths.
    This source contract does not sign or verify the clock provider.
64. Keep the high-fanout logger's three runtime declarations explicitly unsafe.
    `rt_env_get` is nullable and must remain `text?`; its four lazy-init reads
    and the two stderr calls are lexical. Do not add work to the disabled-log
    integer-comparison fast path or turn a missing environment variable into a
    foreign-call success claim. Signing and provider verification remain absent.
65. JWT and password-reset timestamp validation must use the shared integer
    `rt_time_now_unix_micros` ABI, not the cross-lane-incompatible legacy
    seconds symbol. Lift its negative sentinel to `Result`; all security
    consumers must fail closed before expiry/token processing. Preserve one
    clock read per operation, then require artifact-bound admission before
    calling the provider verified.
66. TLS certificate and OIDC expiry validation use the same integer clock
    contract. Certificate validation returns false on clock failure; OIDC
    returns `Err`. Neither consumer may retain the legacy float-interpreter/
    integer-native seconds ABI or add a second clock read. This is fail-closed
    containment only, pending signed artifact-bound provider evidence.
67. Tiered-JIT diagnostics use the shared monotonic microsecond ABI, not the
    legacy wall-clock float declaration. Preserve exactly two clock reads per
    compilation, report a negative timing sentinel on clock failure/regression,
    and never add invalid timing to the aggregate. This is a cold diagnostics
    path and does not establish signed provider admission.
68. Dashboard statistics metadata uses the same shared integer wall-clock ABI.
    A failed read stores the explicit `-1` non-success timestamp rather than
    truncating it to epoch zero; collection still performs one read. Redis
    time failure needs a separate command-protocol contract, so do not collapse
    it into this metadata-only change.
69. Redis TTL dispatch uses one shared integer wall-clock read per inbound
    chunk. A negative result closes the connection before dispatch rather than
    retaining stale/fabricated time. Keep the read count, parser, and successful
    request loop unchanged; artifact signing and verification remain separate.
70. Preserve the legacy `rt_time_now_seconds -> i64` C ABI in every lane.
    Fractional seconds are a different `rt_time_now_seconds_f64 -> f64`
    provider and must be declared/called by that exact name in bootstrap code.
    The Rust interpreter must return `Value::Int` for the integer symbol and
    `Value::Float` only for the f64 symbol. Keep both direct, inline calls;
    do not add conversion allocations, lookup, locking, retries, or extra
    clock reads. This resolves a representation defect, not provider signing.
71. Keep bootstrap `sys.sffi.time` as a raw unsafe-only declaration facade.
    Its legacy millisecond and sleep symbols have no owned runtime backing in
    this tree, so they may not be promoted to safe wrappers or be called
    verified. The supported integer seconds and nanosecond declarations also
    remain unsafe pending artifact-bound provider admission.
72. Keep the interpreter environment-handle facade explicitly unsafe. Its
    registry-backed handles, `auto` values, nil-missing-variable behavior, and
    snapshot/release lifetime cannot be represented as an ordinary native-safe
    ABI. The one Simple proof-of-concept caller must use a minimal lexical
    FFI scope; no allocation, lookup, lock, copy, or call is added to it.
73. Keep the app-I/O compatibility hub's 11 remaining random/log/volatile
    declarations lexically unsafe. Four pointer-bearing log/volatile wrappers
    remain public unsafe APIs; scalar random/configuration wrappers remain
    direct. Do not add marshaling, allocations, lookup, locks, retries, or an
    extra dispatch to compatibility hot paths.
74. Keep the interpreter error-handle facade unsafe-only. Its opaque handles
    are allocator/registry owned by the Rust interpreter, with throw consuming
    the handle. The evaluator's 18 existing error-only raw calls must remain
    in smallest lexical scopes; normal evaluation gains no work.
75. Keep the interpreter AST facade unsafe-only. Its 29 registry-owned raw
    handle declarations and all 14 proof-of-concept evaluator access/release
    calls must retain lexical FFI scopes. Do not copy AST data, add lookups, or
    alter the evaluator's direct access/release call count.
76. Keep the source-only SFFI census honest and useful: report lexical raw-call
    counts only as a source estimate, never as backing, ABI proof, provider
    admission, or signature evidence. Preserve its linear source scan and use
    the metric to prioritize scope containment without adding call-time work.
77. Keep SIMD text/index contracts unsafe until exact runtime provider
    admission exists. The 20 declarations and 15 hot width/UTF-8 calls must
    remain direct lexical scopes; positive index-handle checks and negative
    search/index sentinels retain their current semantics with no extra copy,
    lookup, allocation, lock, retry, or call.
78. Keep Engine scalar math wrappers explicit raw-FFI boundaries. The 2D
    owner has three and the 3D owner one scalar declaration/direct wrapper;
    all remain tagged and lexically scoped. Do not introduce a helper indirection,
    allocation, copy, lookup, lock, retry, or additional provider invocation;
    the source-shape check is containment evidence only, not ABI, artifact,
    signature, or semantic-provider verification.
79. Keep noise, statistics, ML metrics, linear algebra, and vector-distance
    scalar math FFI boundaries explicit. Their five declarations and ten direct
    calls retain lexical scopes and their existing loop/call shape. Do not introduce
    helper dispatch, allocation, copying, lookup, locks, retries, or additional
    provider calls. Source-shape containment is not provider verification or
    signed artifact admission.
80. Keep GPU Engine3D color and math-hook scalar bridges explicitly unsafe.
    Their five direct `f32`/`f64` scalar calls must keep their existing casts,
    call count, and lexical scopes. Do not add temporary allocation, copying,
    helper dispatch, lookup, lock, retry, or extra provider invocation; source
    containment does not establish ABI verification or artifact signing.
81. Use `sffi-unsafe-backlog.shs` as the canonical source-only queue for
    untagged owned Simple extern declarations. It must emit file, line, symbol,
    conservative raw-call estimate, signature fingerprint, tag/contract/provider state, and never call an
    untagged declaration safe, verified, or signed. Keep it audit-time only.
82. Keep `app.check.main`'s transient scope and monotonic-clock SFFI direct.
    Its boolean scope success/failure contract remains `bool`; its three clock
    reads and two scope calls require lexical unsafe scopes. Do not introduce
    numeric substitutes, helper dispatch, allocation, copying, lookup, locks,
    retries, or extra calls. This is source containment, not provider admission.
83. Keep the WM lane-boundary gate on `read_file_text_result`, not a local raw
    non-optional file-text declaration or an empty-text fallback. An unreadable
    baseline/path must return gate `ERROR`; normal operation retains one read
    per path with no retry, extra I/O, lookup, lock, or copy. The canonical
    facade's raw provider remains separately unsafe pending admission.
84. Keep bootstrap CLI argument acquisition and seed native-build dispatch as
    two explicit raw FFI boundaries. Do not add a broader import/facade to the
    bootstrap closure, allocate/copy arguments, add lookup/locking/retries, or
    issue another native-build call. These remain unsafe pending exact ABI and
    artifact-bound provider evidence.
85. Keep the bootstrap argument probe's raw array acquisition explicit and
    lexical. Preserve its one call and avoid bootstrap imports, array copies,
    lookup, locking, retries, or additional argument reads; it remains unsafe
    until the exact provider ABI/artifact has been admitted.
86. Keep the quick C-codegen sample on `read_file_text_result`; unreadable
    input must diagnose and return instead of becoming fabricated empty source.
    Preserve one normal read and one `generate_c_code` call; do not add retries,
    extra I/O, copies, lookup, locks, or code-generation passes.
87. Keep the dashboard remote-session collector's one raw session-file read
    explicitly unsafe until its public collection API gains an error channel.
    Do not silently interpret an unreadable session file as absence; preserve
    its one direct call with no retry, extra I/O, copy, lookup, lock, or task
    fabrication.
88. Keep dashboard schedule/daemon file reads explicitly unsafe until their
    collection results can carry typed I/O failure. Do not turn unreadable
    schedule or lock files into absent tasks; preserve two lexical direct reads
    with no retry, extra I/O, copy, lookup, lock, or task fabrication.
89. Keep the dashboard scheduler's task-list API result-typed. An unreadable
    persisted task must stop cancel/tick processing rather than fabricate an
    absent task; normal scheduling preserves one read per task file and no
    retries, extra I/O, copies, lookup, locks, or duplicate task dispatch.
90. Keep persisted play-session reads explicitly unsafe while the public load
    API returns `Option` and cannot distinguish I/O failure from absence. Do
    not fabricate `None` or empty sessions; preserve two lexical direct reads
    with no retry, extra I/O, copy, lookup, lock, or session fabrication.
91. Keep Portal static-asset reads on `read_file_text_result`; a post-existence
    read failure must produce HTTP 500 rather than empty/fabricated content.
    Preserve one normal read and response build with no retries, extra I/O,
    copies, lookup, locks, or duplicate response generation.
92. Keep Portal template reads explicitly unsafe while the rendering API uses
    empty-view fallback and has no typed I/O error channel. Preserve its one
    direct read with no retry, extra I/O, copy, lookup, lock, or duplicate
    rendering; a result-typed rendering design is required before safe lifting.
93. Keep benchmark report persistence on `read_file_text_result`. If an
    existing metrics table cannot be read, block the append instead of writing
    a fabricated empty replacement. Preserve one normal read/write per table
    with no retry, extra I/O, copies, lookup, locks, or report-generation pass.
94. Keep the all-file parse probe on `read_file_text_result`; unreadable list
    or source input must exit nonzero before parsing. Preserve its normal one
    read per input and one parse per listed source with no retry, extra I/O,
    copies, lookup, locks, or duplicate parsing.
95. Keep the minimal child test runner's source/coverage reads and procfs
    resolver explicit lexical unsafe boundaries. Preserve its eleven direct
    calls and outcome semantics; do not add result-object plumbing, retries,
    extra I/O, copies, lookup, locks, or test execution/coverage passes until
    its narrow helper APIs can carry typed provider failures.
96. Keep cross-reference lint on safe I/O facades. Unreadable test or
    requirement input must emit `XREF005` and stop the affected analysis rather
    than creating misleading missing/unknown-reference warnings. Preserve the
    normal read/scan count without retries, extra I/O, copies, lookup, locks,
    or duplicate lint passes.
97. Keep optional monomorphization-cache persistence explicitly unsafe and
    lexical. Unreadable persistent cache remains a cache miss by design; do
    not add retries, extra I/O, copies, lookup/lock work, or any overhead to
    the in-memory O(1) lookup/store hot path pending provider admission.
98. Keep SMF hot-reload disk wrappers explicit lexical unsafe boundaries. Their
    existing `HotReloadResult.IoError` paths must remain authoritative; preserve
    four direct disk calls with no retries, extra I/O, copies, lookup/lock work,
    or change to hot-reload/update semantics pending provider admission.
99. Keep backend C compilation on `read_file_text_result` for source input;
    unreadable input must exit nonzero. Retain raw bootstrap-argument and
    generated-output-write operations as lexical unsafe calls, with exactly one
    normal argument read, source read, and output write and no retries/copies.
100. Keep backend exhaustiveness-validator source reads explicitly unsafe until
    its per-file result can carry typed I/O error. Preserve one direct lexical
     read with no retry, extra I/O, copy, lookup, lock, or duplicate analysis;
     never convert unreadable backend source to an empty successful validation.
101. Do not promote any contained `rt_*` boundary to verified or signed from
     source evidence. The external admission task is tracked in
     `doc/08_tracking/todo/sffi_v2_provider_admission_2026-08-27.md`: bind the
     exact artifact, ABI/ownership contract, verification receipt, and trusted
     signature before loader publication. Keep the hot path as a cached typed
     call plus required validation; do not add per-call hashing, lookup,
     signature work, allocation, copy, lock, retry, or provider call.
102. Use `scripts/audit/rt-unsafe-priority.shs` only as a source-only textual
     ordering hint for direct `rt_*` migration debt. Its per-module+symbol
     estimate can include strings/docstrings and must never be called a lexical
     call count, reachability result, ABI proof, or admission result.
103. A reviewed mechanical change must first pass the exact module+symbol
     mapping in `scripts/audit/rt-unsafe-autofix-contract.shs POLICY.tsv`.
     It checks only unsafe-tag, contract, and source state, rejects wildcard or
     ambiguous mappings, and does not modify source. Keep the string/docstring/
     comment sabotage coverage in
     `test/01_unit/scripts/rt_unsafe_priority_contract_test.shs`.
