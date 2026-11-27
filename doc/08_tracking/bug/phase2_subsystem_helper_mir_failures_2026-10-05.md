# Phase 2 subsystem test helpers fail MIR lowering

Status: OPEN (P1). No subsystem test binary or test execution is proved by this run.

## Reproduction and evidence

Diagnostic packet: `six-products-current-proven-transport1` under the Windows
restart evidence directory. Producer source: `916be6c20617637e2cccf3d18c23669470ab8ffe`.
Producer SHA-256: `2b83155910336e56ec8b663c3d3e7d3ceb9c61b60fa98182163f9670ff044c33`.
The six compiler/interpreter/loader lanes across LLVM and Cranelift each completed
source inventory with exit zero, then generator and main-verdict helper builds
each returned exit one. Product matrices report required helper compilation
failure and unknown registered/executed/pass/fail test counts. These are twelve
helper build failures, not twelve failed test cases.

`helper-build-failures.json` preserves extracted diagnostics for all six lanes.
The LLVM compiler lane contains 27 distinct generator error lines and 11 verdict
error lines; these are diagnostic counts, not independent root-cause counts.
Completed step receipts retain command, output hashes, actual exit and process
closure. Preserve this packet and its caches for comparison with the successor.

## Parallel diagnosis

- Generator/frontend: `FlatPoolReader` constructor and method resolution in
  `flat_pool_codec.spl`, and `ord` resolution in `placeholder_lambda.spl`.
- Shared I/O/type propagation: `Result` methods and process handle methods in
  `nogc_sync_mut/io/process_ops.spl`, `ProcessObservationPacketKindV4` operator
  lowering, enum arm lowering, an I64 collection iteration, and string methods
  in `nogc_sync_mut/io/env_ops.spl`.

These groupings assign investigation; a diagnostic mentioning a struct does not
prove an enum identity defect. Existing dictionary typed-local workarounds are
applicable only after tracing the actual value's owner and type.

## Repair and acceptance

Use minimal reviewed source repairs or bug-linked semantic-preserving workarounds
with the current producer first. Keep frozen inputs immutable and carry forward
only valid caches. Do not remove tests, stub helper behavior, substitute a seed,
or count generator builds as subsystem test execution.

Compile and execute the real generator and verdict helpers, produce all six
native subsystem products, enumerate each binary's registered tests, then run
each binary through completion with truthful counts and closure evidence.
Qualify root fixes with reproductions and neighboring cases before retiring
workarounds on an isolated later rebuild. Check memory and behavior for every
performance-related repair, and performance and behavior for memory repairs.

**Revalidated 2026-11-02: still plausible because OPEN (P1). No subsystem test binary or test execution is proved by this run; no merged fix commit with a passing regression is cited in this doc.**

## 2026-11-03 s3g4 lane: deferred (concrete blocker)

The diagnostics (`helper-build-failures.json`, 27+11 error lines) live in a Windows
evidence dir that is not in the repo or on this host, and the failures are in pure-Simple
MIR lowering, which the seed cannot execute. Needs the helper builds re-run on the
current producer to regenerate the diagnostic lines before a per-site fix can be written.

## 2026-11-03 blocker (lane p1blk)

Correction: the premise is NOT stale. `FlatPoolReader` still exists (`flat_pool_codec.spl:111`, constructor `:143`); only the cited line moved.
The codec was reworked to the v4 frame (`flat_pool_codec.spl:30-45`), so the
`FlatPoolReader` diagnostic premise may be stale. It cannot be confirmed or closed without
re-running the six-lane generator/verdict helper builds on a current Phase 2 producer.
`helper-build-failures.json` from producer 916be6c2 is the only diagnostic, and it predates
the rework. Next step: rerun the helper builds on the current candidate and re-scope from
the fresh diagnostics.

## 2026-11-05 p1c-p2sub premise check: still valid, still blocked (no code change)

- Premise is not outdated by current policy (nil-as-absence, panic-free, no-Any,
  mono removal): the reported failures are MIR-lowering resolution defects
  (`FlatPoolReader` static ctor/method resolution, `ord`, `Result`/process-handle
  methods, enum arm lowering, I64 collection iteration), not policy-shaped code.
- Named sites still exist on `origin/release/1.0.0`:
  `src/compiler/10.frontend/core/flat_pool_codec.spl:111` (`pub class FlatPoolReader`,
  `static fn new` at :143), `src/compiler/10.frontend/desugar/placeholder_lambda.spl`
  (path moved from the original note), `src/lib/nogc_sync_mut/io/{process_ops,env_ops}.spl`.
  No commit on the branch cites this bug id as fixed.
- Not reproducible today: the `helper-build-failures.json` packet is not on this
  host or in the repo; the failing path is pure-Simple native MIR lowering, which the
  Rust seed (`bin/simple.exe`) does not exercise; stage3 is not deployed yet (phase 3
  still building). A seed-side repro would prove nothing about this defect.
- Action: keep OPEN, P1. Unblock condition: a deployed stage3/self-hosted compiler;
  then re-run the generator + main-verdict helper native builds for the six lanes,
  capture fresh diagnostics, and write per-site repro specs (TDD) before fixing.

## 2026-11-07 mir-p2: interpreter-level MIR repro of the FlatPoolReader site — clean

Correction to the earlier "the seed cannot execute pure-Simple MIR lowering"
notes: the interpreter runs the real `50.mir` lowering. New spec
`test/01_unit/compiler/50.mir/flat_pool_reader_mir_lowering_spec.spl` parses the
REAL `flat_pool_codec.spl` plus a consumer (`FlatPoolReader.new`, `new_bounded`,
`r.ok`, `r.reject_malformed`, `flat_pool_dec_i64(r)`), lowers both to HIR and MIR
in a 2-module closure, and reports **zero** `FlatPoolReader` constructor/method
diagnostics; the only codec diagnostics are the deliberately absent deps
(`text_byte_len`, `env_get_opt`). 3/3 green, non-vacuity case
(`r.nope_missing(1)` -> `unresolved method call`) included. It was never red, so
it is a regression guard, not proof of a fix. Read with the v4 codec rework: the
`FlatPoolReader` part of the 916be6c2 diagnostics is likely stale. Status stays
OPEN: the other groups (`ord`, process_ops/env_ops `Result`/handle methods,
enum arms) and the native helper builds themselves still need a native producer.

## Reopened 2026-11-07

PR #7408 changed these rows on seed-only evidence, which is insufficient. Stage3 (native) still fails: on s3_fable54m, s3_fable56 and s3_fable57s the 12-line fixture C:/dev/p3new/s3sanity/root/test/s3sanity/vb_mm1.spl (struct + impl method + one call) fails during HIR lowering with `[simple-runtime][error] rejected invalid array handle before dereference` followed by `unresolved method call: get route=runtime-fallback key=test.s3sanity.vb_mm1.Custom::get struct_method_syms=yes record_instance_method=n/a lookup_method_in_type=no receiver_has_type=false`. The same file without the call passes; fixture test/fixtures/compiler/native_entry_own_class_methods has the same shape. Status: OPEN, root-cause lane in progress.

## 2026-11-08 lane-f-p2helper: helpers rebuilt on the frozen stage2; one in-scope site fixed, rest re-scoped

**Unblocked without stage3.** The frozen pure-Simple stage2 `C:/dev/p3new/stage2.ef0681fc0e1.exe`
(source `ef0681fc0e1`, 2026-10-27) is on this host and IS the Phase 2 producer this bug is
about. Both helpers were rebuilt with it on `origin/release/1.0.0` @ `01a8acae210`
(`native-build --entry-closure --mode one-binary --go-to-end --keep-going --backend llvm`,
sources `src/lib src/app src/compiler`, 8 GB cap, logs under the lane scratchpad
`p2helper/out-{verdict,generator}/native-build.log.err`):

| helper | wall | peak RSS | objs | `[go-to-end] failed stage=mir` lines |
|---|---|---|---|---|
| `compiler_subsystem_main_verdict/main.spl` | 309 s | 3.35 GB | 0 | 38 |
| `compiler_subsystem_product_generator/main.spl` | 470 s | 6.32 GB | 0 | 54 |

Fresh diagnostics, de-duplicated:

1. **In scope, fixed here** — `process_ops.spl:2161` `process_spawn_piped_owned_v2`:
   `enum construction '…PipedProcessOwnedSpawnV2.CleanupRequired': payload type mismatch at 1:
   nil outside unsafe into optional payload slot (declared 'PipedProcessRefV1?'); use None`.
   Workaround (tagged `@workaround bug=phase2_subsystem_helper_mir_failures_2026-10-05`): the
   `case None` arm passes the matched `reference` (`PipedProcessRefV1?`, value `None`) like its
   sibling arms instead of a bare `nil` literal. Behaviour-identical.
2. **In scope (frontend group), worked around here** — `collection_feedback.spl` (landed
   2026-11-06): all four assignments to `_parser_collection_site_labels` (`:24, :140, :314, :321`)
   fail `assignment target has no local binding` because it is declared `var …: HashMap? = None`;
   its sibling declared `= nil` (`:16`) lowers. This is the known frozen-stage2 defect
   `stage2_module_global_assign_no_binding_2026_11_01` (compiler fix `404747cc60a` postdates the
   frozen binary); its documented `= None` -> `= nil` workaround is applied and tagged under that id.
   Tree re-scan: the only other `var X: T? = None` module globals are
   `src/app/io/feature_registry.spl:14-16` (not in either helper's closure; left for that bug's owner).
3. **Out of scope — post-freeze method vocabulary, NOT a type-propagation defect** — 45 (generator)
   / 36 (verdict) × `unresolved method call: byte_len` in `lib.common.string_core`,
   `build_manager.{contracts,codec}`, `lexer_struct`, `parser`, `_ParserPrimary.*`,
   `placeholder_lambda`, and 4 × `unresolved method call: fill_span` in `crypto/secure_memory.spl`.
   `byte_len` (`4183b795175`, 2026-11-07, ~1080 sites tree-wide) and `Array.fill_span`
   (`f680394dddf`, 2026-11-07) have **zero** occurrences in `src/compiler` at `ef0681fc0e1`: no
   pre-2026-11-07 producer can lower current stdlib. Tracked under
   `llvm_seed_text_byte_len_dispatch_2026-11-07` (note added there). Reverting an 1,080-site
   migration is not this lane's call; the helper builds stay red until a post-11-07 stage2 is frozen.

Premise verdict: the 2026-10-05 groups are now accounted for — `FlatPoolReader` (guard spec green,
2026-11-07), `ord` (`cb4b2cb66b7`, 2026-10-05), `Result`/process-handle methods
(`methods_mir_2026-10-31`, 7 tagged sites), `env_ops` `text?` (`native_helper_provider_globals_and_receivers_2026-10-05`),
enum payload (this change). `ProcessObservationPacketKindV4` operator / I64 iteration produced no
diagnostic on the current producer.

Specs: `test/01_unit/compiler/50.mir/enum_optional_payload_nil_literal_phase2_helper_spec.spl`
(red on `process_ops.spl:2161` and on `collection_feedback.spl:18` before the edits, green after;
MIR non-vacuity case proves the interpreter-run `50.mir` emits the same "use None" rejection;
`None` literal and `T?` local lower clean). Existing guards re-run green on this branch:
`flat_pool_reader_mir_lowering_spec` 3/3, `named_field_projection_provenance_spec` 5/5.

Status -> `fix-implemented-verification-pending`. Unverified: the helpers producing objects/binaries
(blocked by item 3) and six-lane product execution.
