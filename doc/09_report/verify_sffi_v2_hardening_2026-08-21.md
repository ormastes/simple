# SFFI v2 hardening verification — 2026-08-21

## Scope

Verification covers the bounded P0 return-contract, dynamic-interpreter, and
native status-path changes plus the P0/P1 research, requirements, architecture,
design, plans, guide, and executable specification. P1 typed registry/thunks
and P2-P6 remain planned and are not claimed complete.

## Results

- PASS: `simple-runtime` focused `wsffi_native` tests — 4 passed, 0 failed,
  0 ignored.
- PASS: numbered-artifact guards for working and staged changes.
- PASS: direct-env/runtime guards for working and staged changes.
- PASS: `doc/06_spec` contains zero executable `*_spec.spl` files.
- PASS: changed-diff whitespace check after documentation cleanup.
- PASS: focused return-contract tests — 5 passed, 0 failed, 0 ignored.
- PASS: focused dynamic-SFFI tests — 12 passed, 0 failed, 0 ignored. Their
  stable-code assertions inspect the authoritative rich diagnostic context.
- PASS: the tracked dispatch profiler is restored to the interpreter module
  tree, removing the upstream `E0433` compiler-test blocker.
- FAIL: pure-Simple SPipe/docgen and required compiler/lib/MCP smoke checks
  cannot be admitted: the deployed `bin/simple` reports that it is a Rust-built
  bootstrap seed, so it is not valid self-hosted production evidence.
- FAIL: sabotage and cross-lane interpreter/JIT/native/SimpleOS evidence are
  incomplete.
- FAIL: native generic i64/f64 value bridges still collide on zero for invalid
  inputs; migration to status/out or `Result` ABI is tracked in the dynamic
  SFFI bug record.

## Status

**STATUS: FAIL** — the bounded Rust-backed P0 unit tests pass, but this remains
an explicitly partial hardening and design checkpoint, not release evidence or
a claim that SFFI v2 is complete.

## Follow-up: interpreter debug raw boundary (2026-08-26)

- PASS (static): both interpreter-debug facades retain 12 used raw declarations,
  each explicitly `unsafe(ffi)` and each call lexically scoped. Their parity
  audit passes, as does the canonical debug authority audit.
- PASS (source check): `bin/simple check` accepts both changed files. The tool
  identifies itself as the Rust bootstrap seed, so this is not a self-hosted
  production-verification result.
- PASS (optimizer review): each mirror reports the same 55 pre-existing
  opportunities, including two collection-capacity suggestions; the status
  repair adds no normal-path loop, allocation, copy, lookup, hash, or dispatch.
- PASS (contract): provider `-1` failures for breakpoint add/remove and nonzero
  CLI-run status now become `Result.Err`; ordinary boolean behavior is unchanged.
- FAIL (global admission): no signed artifact-bound provider admission is
  established by this work. This follow-up does not change the overall FAIL
  status above.

## Follow-up: advanced scalar math raw boundary (2026-08-26)

- PASS (static): twelve fixed-`f64` declarations and thirteen calls in the
  canonical advanced-math facade are explicitly and lexically `unsafe(ffi)`;
  the guard confirms the Rust exports and no per-call admission machinery.
- PASS (behavior): `math_advanced_spec.spl` executes 13/13 examples with zero
  failures; NaN/infinity remain values rather than fabricated error signals.
- PASS (performance review): direct scalar call shape is retained; optimizer
  reports 25 MIR bounds-check opportunities and zero general patterns.
- WARN: checks ran through the bootstrap seed, not a self-hosted production
  binary. No signature or artifact-bound evidence was created, so global SFFI
  admission remains FAIL.

## Follow-up: interpreter error-handle owner (2026-08-26)

- PASS (static): nine canonical raw calls are explicitly and lexically
  `unsafe(ffi)`; the compatibility facade has no raw declarations.
- PASS (source): both canonical and compatibility modules check successfully;
  the owner audit verifies interpreter-provider symbols and no lexical bypass.
- PASS (performance review): compatibility now re-exports with no runtime
  wrapper; optimizer reports 18 MIR-only opportunities and zero general ones.
- FAIL (global admission): error handles remain interpreter-owned opaque values
  without artifact-bound signature/evidence admission or cross-lane proof.

## Follow-up: counterpart ABI boundary (2026-08-26)

- PASS (source/static): nine raw dlopen/opaque-handle calls are lexical
  `unsafe(ffi)`; the guard rejects nil-to-empty coercion and call-time admission.
- PASS (performance review): no new lookup/hash/dispatch/allocation path;
  optimizer reports one pre-existing general capacity suggestion.
- FAIL (runtime): the deployed bootstrap artifact reports unknown
  `rt_counterpart_open`/`rt_counterpart_probe_abi`; 7 of 8 focused examples
  fail before provider invocation. This is artifact parity, not a pass.
- FAIL (global admission): no signed provider/evidence admission is established.

## Follow-up: evidence-admission key algorithm policy (2026-08-26)

- PASS (targeted contract): evidence admission accepts the valid provider-
  scoped Ed25519 fixture and rejects a trusted RSA key before raw-signature
  verification; existing artifact, report, trust, canonicalization, and
  substituted-signature sabotage cases also pass.
- PASS (performance scope): public-key inspection happens only during provider
  admission. No SFFI call path, allocation, copy, registry lookup, hash, or
  dispatch changed.
- FAIL (global admission): this hardens the verifier but supplies no exact
  signed provider artifact job, so the repository-wide signed-admitted count
  remains zero and SFFI is not globally verified.

## Follow-up: AES-XTS raw boundary (2026-08-26)

- PASS (source/static): three raw declarations and sixteen call sites are
  explicit lexical `unsafe(ffi)`; the owner audit also confirms the Rust
  inverse-block provider and no call-time admission/generic dispatch.
- PASS (performance review): direct calls and allocation shape are unchanged;
  optimizer reports 113 MIR-only opportunities and zero general patterns.
- WARN (behavior): the existing IEEE 1619 KAT remains blocked by the known
  upstream interpreter `u8` array-lifting defect, so it was not rerun here.
- FAIL (global admission): this provides neither a signed artifact job nor
  cross-lane proof; global SFFI admission remains zero.

## Follow-up: channel admission status (2026-08-26)

- PASS (static): all six raw channel declarations and thirteen calls are
  lexical `unsafe(ffi)`; the guard verifies the `i64` send status is retained
  by Simple, interpreter, and both provider backends.
- PASS (performance review): `try_send` replaces a closed-state query plus
  ignored send with one direct status-returning send. Optimizer reports 19
  MIR-only opportunities and zero general patterns.
- WARN (verification): focused Rust unit compilation is blocked by unrelated
  missing imports in `interpreter/expr/collections.rs`; the deployed bootstrap
  executable retains the prior void result and its Simple spec therefore fails
  one open-channel assertion. Neither is counted as a pass.
- FAIL (global admission): channel providers remain unsigned and lack exact
  artifact/cross-lane admission evidence.

## Follow-up: MIR actor and synchronization status ABI (2026-08-26)

- PASS (static/source): the MIR actor bridge now declares the Rust provider's
  actual spawn and receive signatures. Mutex unlock and rwlock store retain
  their `i64` status returns, and all touched raw calls are lexical
  `unsafe(ffi)`. The synchronization authority guard passes.
- PASS (performance review): the repairs only correct existing argument and
  status propagation. They add no loop, allocation, copy, hash, lookup,
  generic dispatch, or per-call admission work.
- FAIL (semantic facade): `src/lib/nogc_sync_mut/concurrent/actor_hooks.spl`
  still exposes an incompatible actor ABI and is deliberately not classified
  as a safe runtime wrapper. It needs a scheduler-owned pure-Simple migration
  or generated contract, not an annotation-only workaround.
- FAIL (global admission): no exact signed provider artifact/evidence job is
  available. This report remains **STATUS: FAIL** for global SFFI safety and
  verification.

## Follow-up: legacy actor-hook ABI retirement (2026-08-27)

- PASS (static/source): the compatibility actor-hook module has no raw
  `rt_actor_*` declaration or call. The authority guard passes, and the
  affected-source check accepts both the retired facade and its consumer.
- PASS (performance review): full optimizer analysis reports no opportunity in
  the retired module. Removing the invalid foreign call path adds no hot-path
  allocation, copy, loop, lookup, hash, or dispatch.
- PASS (fail closed): stale callers get
  `E-SFFI-ACTOR-LEGACY-ABI` and are directed to scheduler-owned pure-Simple
  actors rather than passing `Any` values through an incompatible runtime ABI.
- FAIL (global admission): this removes one unsafe island only. A direct
  `extern fn rt_*` source scan finds 5,337 declarations; the broader
  source-only ledger has 12,739 foreign rows, 3,407 unsafe-tagged, zero
  signed-admitted, and 8,940 untouched (11,115 are `rt_*` rows). It cannot
  observe provider language without an admitted binary. No exact signed
  provider artifact/evidence admission exists for the global set. Overall
  status is still **FAIL**.

## Follow-up: canonical I/O ambiguous-return scopes (2026-08-27)

- PASS (static/source): the canonical I/O owner has 28 lexical raw-call
  scopes. Its authority audit specifically checks the four raw text/hash
  facades that remain unsafe because their ABI cannot distinguish error and
  ownership from a valid `text` result.
- PASS (performance review): source check and full optimizer analysis pass.
  The direct calls retain their result and execution shape; no allocation,
  copy, loop, lookup, hash, or dispatch was added.
- FAIL (global admission): lexical scope does not supply nullable/status-out
  ABI, artifact-bound evidence, or a provider signature. The global SFFI
  verification status remains **FAIL**.

## Follow-up: compiler CAS raw-owner consolidation (2026-08-27)

- PASS (static/source): six raw CAS filesystem/process/time declarations are
  unsafe-tagged and called only by six private always-inline lexical owners;
  the CAS authority audit and affected source check pass.
- PASS (performance shape): callers retain their existing direct ABI calls
  after inlining. No retry, lock, lookup, allocation, copy, loop, or dispatch
  was added by this containment repair.
- WARN (optimizer backlog): full analysis reports 70 opportunities in the
  pre-existing cache module (64 MIR; six general preallocation/length-hoist
  findings). No benchmark establishes a regression or an optimization benefit;
  this is recorded for a dedicated CAS workload, not treated as fixed.
- FAIL (global admission): no artifact-bound signature or semantic provider
  evidence has been added. Global SFFI verification remains **FAIL**.

## Follow-up: compiler fast-GC raw-owner consolidation (2026-08-27)

- PASS (static/source): twelve raw filesystem/directory/time contracts are
  unsafe-tagged and reachable only through twelve private always-inline lexical
  owners. The focused authority audit and source check pass.
- PASS (performance shape): no retry, allocation, copy, lock, lookup, or
  dispatch was added; inlining preserves one direct ABI call per owner.
- WARN (test): `cache_v2/gc_spec.spl` runs nine functional examples, then its
  unrelated lease-source-text example fails with `semantic: variable dir not
  found`. It does not import or invoke `fast_gc.spl`, so this is not counted as
  a regression or PASS.
- WARN (optimizer): 58 existing fast-GC opportunities remain, including the
  current selection sweep. No benchmark supports a performance claim.
- FAIL (global admission): no exact artifact/provider signature or semantic
  evidence exists. Global SFFI verification remains **FAIL**.

## Follow-up: compiler cache-admission raw-owner consolidation (2026-08-27)

- PASS (static/source): four raw admission filesystem/directory contracts are
  unsafe-tagged and isolated in private always-inline lexical owners. The pin
  reader uses canonical `file_read_nullable`; the authority audit and source
  check pass.
- PASS (performance shape): no loop, allocation, copy, lookup, or dispatch
  was added. Full optimizer analysis reports 22 existing module opportunities
  (21 MIR, one preallocation) for a separate measured optimization task.
- WARN (contract): `nil` still normalizes to an empty pin set. That retains the
  prior missing-pin behavior but does not distinguish an unreadable existing
  pins file, so this boundary is not promoted to verified safe.
- FAIL (global admission): no artifact-bound provider signature or semantic
  evidence exists. Global SFFI verification remains **FAIL**.

## Follow-up: cache unreadable-input fail-closed repair (2026-08-27)

- PASS (static/source): admission and mark-sweep no longer coerce unreadable
  existing pins/manifests to empty text. They emit stable
  `E-SFFI-CACHE-PINS-READ` and `E-SFFI-CACHE-MANIFEST-READ` fail-closed
  diagnostics after the nullable-read guard. Both authority audits and the
  affected two-file source check pass.
- PASS (performance shape): normal absent-file and successful-read paths keep
  their direct ABI shape. The failure branch adds no allocation, copy, loop,
  lookup, lock, or dispatch; optimizer findings remain 22 and 46 respectively.
- FAIL (global admission): this improves two cache owners only. No
  artifact-bound provider signature or semantic evidence exists for the global
  SFFI set, so verification remains **FAIL**.

## Follow-up: compiler cache-lease raw-owner repair (2026-08-27)

- PASS (static/source): eight raw lease contracts are unsafe-tagged and
  isolated in private always-inline lexical owners. The authority audit and
  source check pass.
- PASS (fail closed): unreadable existing leases raise
  `E-SFFI-CACHE-LEASE-READ` for query paths; reclamation conservatively retains
  them rather than deleting an unverified lease.
- WARN (optimizer): 49 existing opportunities remain (48 MIR, one
  preallocation); no benchmark supports an optimization claim.
- FAIL (global admission): no artifact-bound provider signature or semantic
  evidence exists. Global SFFI verification remains **FAIL**.

## Follow-up: authority census after cache-family containment (2026-08-27)

- PASS (inventory): source authority census reports 14,064 missing call sites,
  2,298 lexical scopes, and 1,625 function-wide unsafe scopes. The cache pass
  reduced missing calls by 96 and added 37 lexical scopes compared with the
  prior 14,160/2,261 snapshot.
- WARN (scope): these are source classifications, not ABI, ownership,
  provider-language, artifact, or cryptographic-signature verification.
- FAIL (global admission): 14,064 unscoped call sites remain. SSH session and
  Torch dynamic operations are the next largest provider families; global SFFI
  safety and signed verification remain **FAIL**.

## Follow-up: compiler mark-sweep raw-owner consolidation (2026-08-27)

- PASS (static/source): seven raw mark-sweep contracts are unsafe-tagged and
  isolated in private always-inline lexical owners; raw text reads are replaced
  by canonical nullable reads. The authority audit and source check pass.
- PASS (performance shape): no retry, lock, allocation, copy, lookup, or
  dispatch was added. Optimizer analysis reports 46 existing opportunities
  (42 MIR, four preallocation) for separate measured work.
- WARN (contract): nil still normalizes to empty pin/manifest content, so an
  unreadable existing input is not yet distinguishable from absence. This
  boundary remains unverified.
- FAIL (global admission): no artifact-bound provider signature or semantic
  evidence exists. Global SFFI verification remains **FAIL**.

## Follow-up: dynamic Torch lexical authority (2026-08-27)

- PASS (static/source): the optional libtorch facade has 61 direct raw calls,
  each in a minimal lexical `unsafe(ffi)` expression; availability uses an
  always-inline lexical owner. Result wrappers continue to reject nonpositive
  handles rather than manufacturing a usable value.
- PASS (performance shape): each result/constructor path retains one direct
  provider call after validation. The source guard rejects explicit allocation,
  copy, lookup, lock, and loop machinery in the facade.
- FAIL (global admission): raw libtorch handles still have legacy ABI and
  ownership limits, and no exact provider artifact, trusted signature, or
  sanitizer/proof receipt was supplied. This module is contained but not
  verified or signed.

## Follow-up: live-backing source census refresh (2026-08-27)

- PASS (inventory): `rt-safety-census.shs` reports 11,113 declaration rows,
  2,966 distinct symbols, 3,123 unsafe-tagged rows, 922 unsafe rows with a
  documented contract, 7,750 untouched rows, and 23,564 lexical call-site
  estimates in this repository-owned census scope.
- FAIL (global admission): verified rows, signature-verified rows, and
  verified-and-signed rows are all zero. The census is source evidence only;
  it cannot establish foreign ABI correctness, ownership, signed artifact
  identity, or semantic provider verification.

## Follow-up: legacy unbacked SSH facade containment (2026-08-27)

- PASS (static/source): all 23 `rt_ssh_*`/`rt_sftp_*` declarations and all 23
  direct calls are explicitly unsafe; calls use minimal lexical FFI scopes.
  The public wrappers remain unsafe because no provider contract exists.
- PASS (performance shape): the source guard rejects explicit allocation,
  dynamic lookup, or locking; direct provider call shape is unchanged.
- FAIL (provider): no runtime implementation, interpreter registration, ABI
  contract, provider artifact, trusted signature, or semantic evidence exists.
  This legacy facade remains unsafe-only and cannot be called verified.

## Follow-up: syscall clock/progress lexical authority (2026-08-27)

- PASS (static/source): nine clock/progress declarations are explicitly
  `unsafe(ffi)` and six executed calls are lexical. Native realtime/monotonic
  failures retain their negative sentinels rather than becoming a timestamp.
- PASS (performance shape): progress init and elapsed retain their existing
  one-clock-read paths; the guard rejects allocation, dynamic lookup, and lock
  work in the owner.
- FAIL (global admission): this is a backed source contract, not a signed
  artifact or semantic verification receipt. The provider remains unsafe and
  unsigned at repository scope.

## Follow-up: logger nullable environment SFFI (2026-08-27)

- PASS (static/source): all three raw logger declarations are `unsafe(ffi)`;
  `rt_env_get` now exposes its nullable result and all six environment/stderr
  calls use minimal lexical scopes.
- PASS (performance shape): logger configuration still reads the environment
  only during lazy initialization, while the disabled-log path remains its
  existing integer comparison. The change adds no call, allocation, or lookup
  to that path.
- FAIL (global admission): no signed logger/runtime artifact or semantic
  provider receipt was created. This is source containment, not verification.

## Follow-up: JWT clock cross-lane ABI repair (2026-08-27)

- PASS (static/source): JWT replaces the legacy seconds symbol—which presents
  as a float in the Rust interpreter lane—with the shared integer microsecond
  ABI. Its negative sentinel lifts into `Result`; JWT validation and reset
  token creation/verification now fail closed on clock failure.
- PASS (performance shape): each affected operation retains one clock read;
  failure handling adds no work to a successful timestamp path.
- FAIL (global admission): the runtime clock artifact is not signed/admitted
  with an exact evidence receipt. This closes a cross-lane contract defect but
  does not globally verify the provider.

## Follow-up: TLS/OIDC clock cross-lane ABI repair (2026-08-27)

- PASS (static/source): certificate and OIDC expiry validation now use the
  shared integer microsecond ABI, each in a lexical unsafe scope. Clock failure
  invalidates a certificate and returns an OIDC validation error.
- PASS (performance shape): both validation paths retain one clock read and no
  added allocation, lookup, lock, retry, or copy on successful reads.
- FAIL (global admission): the clock provider has no exact signed artifact or
  verification receipt, so this is not a provider-verification claim.

## Follow-up: tiered-JIT monotonic clock ABI repair (2026-08-27)

- PASS (static/source): tiered-JIT diagnostics use the shared integer monotonic
  microsecond ABI through one lexical raw owner. Missing/regressed timestamps
  return a negative timing sentinel and are excluded from aggregate timing.
- PASS (performance shape): a compilation still performs exactly two clock
  reads; no allocation, lookup, lock, retry, or hot call-path work was added.
- FAIL (global admission): no signed runtime artifact or verification receipt
  exists, so the provider remains unsafe/unsigned globally.

## Follow-up: dashboard statistics clock ABI repair (2026-08-27)

- PASS (static/source): dashboard metadata uses the shared integer microsecond
  clock in a lexical unsafe scope. A failed clock now records `-1`, not epoch
  zero from integer division.
- PASS (performance shape): collection retains one clock read and adds no
  allocation, lookup, lock, retry, or copy.
- FAIL (global admission): this source contract is not signed provider
  evidence; global SFFI verification remains unavailable.

## Follow-up: Redis TTL clock ABI repair (2026-08-27)

- PASS (static/source): Redis now uses the shared integer microsecond clock in
  a lexical unsafe scope. A clock failure breaks the connection loop before
  TTL-sensitive request dispatch; the existing close path releases the socket.
- PASS (performance shape): successful chunks retain one clock read and the
  existing parser/dispatch loop, with no added allocation, copy, lookup, lock,
  or retry.
- FAIL (global admission): this does not supply a signed artifact or provider
  verification receipt; repository-wide SFFI remains unverified.

## Follow-up: legacy seconds return-representation repair (2026-08-27)

- PASS (static/source): the native `rt_time_now_seconds -> i64` ABI now has
  the same integer representation in the Rust runtime and interpreter. The
  fractional `rt_time_now_seconds_f64 -> f64` provider is separately
  registered and used by the two bootstrap consumers that require subsecond
  time. The authority guard checks both representations and lexical scopes.
- PASS (performance shape): both clock variants remain one direct inline
  provider call. No allocation, copy, lookup, lock, retry, or extra read was
  added to either clock path.
- FAIL (global admission): static/source checks do not establish exact runtime
  artifact identity, trusted signature, ABI admission, or semantic provider
  verification. The provider remains unsigned and unverified globally.

## Follow-up: bootstrap raw time facade classification (2026-08-27)

- PASS (static/source): all four `sys.sffi.time` declarations now explicitly
  carry `unsafe(ffi)`. The legacy millisecond-clock and sleep symbols are
  documented as unbacked in the owned runtime rather than being implied safe.
- PASS (performance shape): declaration-only classification adds no call-path
  allocation, copy, lookup, lock, retry, or clock read.
- FAIL (provider): no artifact-bound provider, ABI contract, signature, or
  verification receipt is present; the entire facade remains unsafe-only.

## Follow-up: interpreter environment-handle containment (2026-08-27)

- PASS (static/source): all 12 exported environment-handle declarations carry
  `unsafe(ffi)`, and the sole Simple proof-of-concept read uses the smallest
  lexical scope. The Rust interpreter provider rejects invalid handles; `nil`
  remains documented only as an ordinary missing-variable result.
- PASS (performance shape): the evaluated read remains one direct provider
  call. The guard rejects added allocation, copy, dynamic lookup, or locking
  in the facade/consumer.
- FAIL (global admission): the Rust interpreter provider has no artifact-bound
  ABI/ownership receipt or trusted signature. This facade remains unsafe-only.

## Source-only SFFI inventory refresh (2026-08-27)

- `SFFI_SOURCE_ONLY=1 rt-safety-census.shs` found 11,106 declaration rows and
  2,966 distinct symbols. It classifies 3,193 rows (2,093 symbols) as tagged
  unsafe, 935 rows as unsafe with a documented contract, and 7,673 rows
  (1,322 symbols) as untouched.
- Implementation definitions observed by language: C 2,378 rows/1,889 symbols
  in 91 files; C++ 219/219 in one file; Rust 2,145/2,122 in 172 files; Simple
  637/623 in 62 files. These are implementation observations, not ABI proof.
- Verified, signature-verified, and verified-and-signed rows are all zero.
  Source-only mode intentionally reports no provider identity/backing; it
  cannot be used to claim global admission or unsafe minimization.

## Follow-up: app-I/O compatibility boundary containment (2026-08-27)

- PASS (static/source): 11 remaining raw random/log/volatile declarations are
  tagged and lexically confined. The four wrappers that accept raw pointer
  ranges or addresses remain explicitly unsafe instead of exposing a false
  safe API.
- PASS (performance shape): scalar wrappers retain one direct call. The guard
  rejects extra symbol occurrences and records no allocation/lookup layer.
- FAIL (global admission): provider identity, artifact admission, signature,
  and semantic verification remain absent at repository scope.

## Follow-up: interpreter error-handle containment (2026-08-27)

- PASS (static/source): nine opaque error-handle declarations are tagged
  `unsafe(ffi)` and all 18 evaluator error-path calls are lexically scoped.
  Handles are documented as interpreter-owned, with throw consuming its input.
- PASS (performance shape): only existing exceptional branches changed; normal
  expression evaluation retains its prior work and raw-call count.
- FAIL (global admission): the interpreter registry/provider is not bound to a
  signed artifact, ABI contract, or verification receipt. It remains unsafe.

## Follow-up: interpreter AST-handle lexical containment (2026-08-27)

- PASS (static/source): the 29 raw AST-handle declarations were already
  tagged, and all 14 proof-of-concept evaluator accesses/releases now use
  smallest lexical FFI scopes.
- PASS (performance shape): the evaluator preserves its exact direct AST
  access/release count with no copies, allocation, lookup, lock, or retry.
- FAIL (global admission): the interpreter registry remains outside
  artifact-bound ABI/signature/verification admission and is unsafe-only.

## Follow-up: source-only unsafe-minimization census (2026-08-27)

- PASS (tooling): source-only mode now performs one linear source scan for raw
  calls inside lexical FFI capability blocks. It reports 1,880 observed calls
  across 1,069 symbols and labels the result
  `source_lexical_estimate_only`.
- PASS (performance shape): the measurement is build/audit-time only; it adds
  no runtime call-path allocation, lookup, lock, copy, branch, or dispatch.
- FAIL (admission): lexical source scope does not prove loaded-provider ABI,
  ownership, artifact identity, verification receipt, or signature. The census
  still reports zero verified-and-signed rows.

## Follow-up: SIMD text/index boundary containment (2026-08-27)

- PASS (static/source): 20 raw SIMD text/index declarations are explicitly
  unsafe, and all 15 hot WidthIndex/UTF-8 calls use direct lexical FFI scopes.
  Existing positive-handle and negative-sentinel behavior is retained.
- PASS (performance shape): the authority guard asserts the exact raw-call
  count; no wrapper, copy, allocation, lookup, lock, retry, or extra call was
  introduced to the hot text path.
- FAIL (global admission): runtime source backing is not exact artifact-bound
  ABI/ownership verification or trusted signature evidence.
