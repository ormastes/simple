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
