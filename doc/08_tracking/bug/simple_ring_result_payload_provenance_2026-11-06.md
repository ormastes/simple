# simple_ring fails Stage 2 MIR: wrong Ok-payload record and untyped Err binder (2026-11-06)

**Status:** defect 1 fixed in source (2026-11-06, needs Stage 2 redeploy to verify); defect 2 open; workarounds kept

Module `lib.nogc_async_mut.async_ring.simple_ring` fails MIR lowering under the Stage 2
compiler with up to two fatal errors. Seen first on the `file_fiber_v1.spl` entry closure
(`mir_generic_trait_bound_receiver_unresolved_2026-11-06`), reproduced on the run-10 Stage 2
compiler (sha256 `43f9a6fc68ac232f...`) with entry `simple_ring.spl` and the phase-C
`compiler_cli_build` argv (`native-build <entry> --backend=cranelift --low-memory`,
`SIMPLE_FILE_WORKERS=0 SIMPLE_BOOTSTRAP=1`, 16G cgroup).

Neither error is a stale source use: `RingResetReceipt` never had a `token` field and no
source reads one from it.

## Defect 1: Ok payload of `Result<RingCompletion<Cpl>?, E>` takes a foreign record (intermittent)

    field 'token' is absent from exact value layout '.../simple_ring.spl::RingResetReceipt'

The record name varies with lowering order (`RingResetReceipt` on the file_fiber closure,
`RingBatchCommitReceipt` on the simple_ring entry) and the error is intermittent: 2 of 5 runs
of the unchanged file. Site: `take_completion` — `case Ok(maybe): if val completion = maybe:
... completion.token`. Bisect: deleting `take_completion` removes it; deleting `commit_batch`
moves the name to `RingResetReceipt`.

Mechanism (`switch_operators_calls.spl`, single-payload bind arm): the subject `retained` is
an untyped local in a generic class method, so `result_variant_payload_type` and
`result_variant_payload_struct_name` both return nothing, and the binder falls back to
`enum_payload_struct_names["Result::Ok"]` — a closure-global, last-lowered-wins slot holding
whichever `Ok(Receipt(...))` was lowered last. The `Rec?` payload then inherits that record.

Seed-run MIR repro (harness of `test/01_unit/compiler/50.mir/missing_struct_field_lowering_spec.spl`):
a `class Ring<Op, Cpl>` with `me take_retained(...) -> Result<Done<Cpl>?, RingErr>`,
`me take(...)` doing `val retained = self.take_retained(id); match retained: case Ok(maybe):
if val completion = maybe: ... completion.token`, and `me reset(...) -> Result<Receipt, RingErr>:
Ok(Receipt(...))` fails with `field 'token' is absent from exact value layout 'app.main::Receipt'`.
The same shape as free functions lowers cleanly. Annotating `retained` makes the seed repro
pass but NOT the Stage 2 build: with `retained` annotated the Ok payload type is the structural `RingCompletion<Cpl>?`, not a named record, so the bind arm still reaches the shared-registry fallback. A guard that skips the global fallback when the instantiated
payload is known to be structural (`T?`, array, tuple, primitive) did not change the seed
repro (the payload type is unknown there), so it was not landed.

## Defect 2: Err binder of an annotated `Result<(), SimpleRingError>` has no payload type (deterministic)

    enum construction '...RingCancelOutcome.CancelRejected': payload type mismatch at 0; function=cancel

`cancel`: `val release_result: Result<(), SimpleRingError> = ...; match release_result: ...
case Result.Err(error): RingCancelOutcome.CancelRejected(error)`. With
`SIMPLE_ENUM_PAYLOAD_PATH_TRACE=1`: `remembered-miss local=81 expected='named#21' line=0`
then `mir-evidence ... mir_present=<invalid-heap:...>` — the `error` binder carries no
remembered HIR type, no source type, and no usable MIR type, so the payload check rejects it.
5 of 5 runs. Not reproduced by the seed-run harness (free function or generic class).

## Workaround (landed)

`simple_ring.spl`, both marked `@workaround bug=simple_ring_result_payload_provenance_2026-11-06`:
- `take_completion`: `val typed_completion: RingCompletion<Cpl> = completion`, read
  `typed_completion.token` and return `Ok(typed_completion)`.
- `cancel`: `val rejected: SimpleRingError = error` then `CancelRejected(rejected)`.

Evidence on the run-10 Stage 2 compiler, same argv: before, the unchanged file failed 5 of 5
(defect 2 every time, defect 1 in 2). After, 5 of 5 runs lower every module through MIR and
codegen and stop only at the link (`undefined symbol: __simple_main`, expected for an entry
with no `main`). Seed specs: `simple_ring_spec` 9/9, `mission_adapter_spec` 10/10,
`simple_ring_rti004_wa_spec` 6/6 (its source-shape pin updated to the new `cancel` arm).

## To close

Fix both MIR defects (give the bound payload the subject's instantiated type when the subject
is a typed method-call result; remember the declared Err type on a Result Err binder), then
remove the two workarounds.

## Defect 1 fix (2026-11-06)

Root cause: `resolved_call_hir_return_type` never answered for a same-module
generic class method. Its primary source `fn_return_types` has no writer, and
the method symbol carries no `Function` type, so `enum_match_expr_type` returned
nil for `self.take_retained(id)`; the untyped `retained` local therefore had no
Result type and the Ok binder fell to the closure-global `Result::Ok` slot.

Fix:
- `expr_dispatch.spl` `resolved_call_hir_return_type`: fall back to the
  module's own `module_fn_declared_returns` (same-module ids).
- `builtin_method_extras.spl` `remember_untyped_let_nominal_init`: record a
  `Result<T, E>` initializer type on an untyped `val`.
- `switch_operators_calls.spl` single-payload bind arm: never apply the
  closure-global record slot when the known payload is structural
  (`hir_payload_type_is_structural`: `T?`, array, slice, tuple, dict, primitive).

Spec: `test/01_unit/compiler/50.mir/result_payload_provenance_spec.spl` (case 1
red before, green after). Case 2 pins defect 2's shape, which still does not
reproduce in the seed-run harness. The two source workarounds stay until a
redeployed Stage 2 compiler builds `simple_ring.spl` without them.

## Re-scope (2026-11-07)
- Defect 1: the source fix stands. `result_payload_provenance_spec` passes 2/2 on the seed run (2026-11-07,
  base 07ed6359433).
- Defect 2 is still not reproducible on the seed. Case 2 is green, and `result_variant_payload_type` already
  answers `Err` from a `HirTypeKind.Result` subject. The stage2 trace (`remembered-miss`) means the binder
  local got no `remember_local_hir_type`. In the current bind arm, that happens only when
  `effective_payload_type` is nil, or on the `exact_err_record` branch (which never records a HIR type).
  Telling these two apart needs a Stage 2 probe. No MIR probe slot was free (`.mir_slot.3` locked), so no
  speculative edit was landed without a failing repro.
- Next step: in a free probe slot, run the stage2 build of `simple_ring.spl` with the `cancel` workaround
  reverted and `SIMPLE_ENUM_PAYLOAD_PATH_TRACE=1`, and log which branch the `Err` arm takes. Then write the
  failing spec for that branch.

## Defect 2: empty-owner branch fixed (2026-11-07, lane p1-ring)
- Stage 2 probe NOT run: no current Stage 2 binary exists (`build/bootstrap/stage2/.../simple.exe.rejected`
  only), and a cold Stage 2 build does not fit the lane budget (41.6 GB free, 24 GB must stay free).
- Seed repro of the lead, now `result_payload_provenance_spec` case 4: a `Result<(), SlotErr>` subject
  whose owner came from a join with an unknown arm (`if c: Ok(()) else: self.release(id)`).
  `join_result_err_record_owners` (and `invalidate_`/conflicting `copy_`) store `""` but keep the key, so
  `contains` made the bind arm take `exact_err_record`. That branch raised "Result Err record has no
  unique provider layout snapshot", never remembered a HIR type for the binder, and so also failed
  with the exact Stage 2 text `payload type mismatch at 0; function=cancel`. Red before, green after.
- Fix (`switch_operators_calls.spl`): `exact_err_record` now needs a non-empty owner. The only exception is
  a subject with no declared payload type, which keeps the fail-closed check. An empty owner with a
  declared `Result` binds from the declaration (and remembers its HIR type).
- Case 3 (exact provider record, non-empty owner) passes before and after. That shows the
  non-empty `exact_err_record` path types the binder correctly on the seed.
- Still open: whether Stage 2's `cancel` reaches the empty-owner branch, or has `effective_payload_type`
  nil (SimpleRingError is an enum, so a provider owner should never be registered for it). Keep the
  `cancel` workaround until a redeployed Stage 2 builds `simple_ring.spl` without it.

## Original failure: fresh reproduction lane (2026-11-07)

Status: original cause unresolved; diagnostic instrumentation and regression
fixtures authored, execution pending. The adjacent enum/shared-record repair
and empty-owner fallback are not proof of the historical cause.

The original producer was the run-10 self-hosted aarch64 Linux compiler,
reported hash prefix `43f9a6fc68ac232f`. Its full producer/source/runtime
receipt and raw defect-2 trace have not been recovered locally. The linked
trait-receiver report names
`build/bootstrap-opus-10/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.log:89052-89098`;
those lines identify the trait failure, **not** an established location of
this Result Err trace. That artifact directory is absent from the inspected
local Windows worktrees.

### Correction to the old trace interpretation

The `mir-evidence` trace executes only after
`if not maybe_actual_mir.?: return false`. Reaching it establishes that the
presence check succeeded. In the old interpolation,
`mir_present={maybe_actual_mir.?}` uses value-position unwrap syntax, so it
formats the `MirType` payload rather than an explicit Boolean predicate.
The printed `<invalid-heap>` does not independently establish a missing or
corrupt MIR local. The missing remembered HIR type remains an observed
boundary; the cause still requires a controlled reproduction.

The isolated diagnostic source changes print scalar MIR-kind information
and `mir_present=true` after the successful guard. An opt-in
`[result-err-bind]` record now reports the subject, binding, raw and bound
LocalIds, selected exact-record/declared/unknown route, explicit Boolean type
presence, and scalar HIR/MIR kinds. It uses the existing
`SIMPLE_ENUM_PAYLOAD_PATH_TRACE=1` gate and does not lower values or write
metadata again. The extra registry reads are diagnostic-only; the route probe
is restricted to Result Err binders. A producer rebuilt from these changes is
needed to execute the new diagnostics; an older executable does not acquire
them by compiling a newer fixture.

### Prepared reproduction and prevention inventory

The private lane starts from release
`98669e12655ab2be54aec09acc118aeb43ee8ff0` in
`D:/dev/simple-result-err-rootcause-20261107`. Its fixtures under
`test/fixtures/compiler/result_err_generic_method_original/` are:

| Fixture | Purpose |
| --- | --- |
| `main.spl` | Minimal original generic method shape; no foreign record or typed Err alias |
| `typed_alias_control.spl` | Same shape with the historical typed-alias workaround, diagnostic control only |
| `free_function_control.spl` | Corresponding free-function calls without a typed Err alias |
| `nested_match.spl` | Result match, slot-state match, then annotated method Result Err reconstruction |

Each standalone candidate asserts two distinct negative Err codes and the Ok
branch before printing its exact success marker. Generic controls also check
their source field; the nested case checks outer rejection and the alternate
slot state. The existing ForeignReceipt fixture remains a separate
coexistence control.

`test/01_unit/compiler/50.mir/result_err_generic_original_binder_spec.spl`
loads these actual fixtures, lowers their parsed HIR/MIR, then checks the
cancel function's bound error local retains `CancelError`, its runtime enum
marker, and exactly one MIR local declaration, without a record-owner entry.
Function/binding counts prevent a missing traversal from passing. This is
metadata coverage, not a substitute for native execution.

For the actual `simple_ring` replay, remove only the cancel arm's typed
`rejected` alias and pass `error` directly to `CancelRejected`. Keep the
`take_completion` workaround to isolate defect 2. No production workaround
has been removed by this preparation.

### Required evidence before an original-cause fix claim

Record the complete producer hash, producer source revision, target, backend,
linked runtime/provider and isolated cache identity for every attempt. Use
`SIMPLE_NO_STUB_FALLBACK=1` where supported. Retain compile/run exit codes and
complete logs, validate real Err/Ok values, and collect the binder route and
scalar metadata trace. Cover both native backends when available.

All-green current fixtures mean "not reproduced on this producer" unless a
controlled affected-producer/source failure and repaired differential are
also retained. The actual `simple_ring` cancel-only replay is a separate
acceptance criterion. Neither source inspection nor the adjacent fixes close
the original report.

The sole bootstrap owner reports no admitted self-hosted runtime or Hello
receipt yet for its active immutable source
`7ffb05cc9abdbf6233d87ae5b3b5449a13febebf`. No Rust seed, rejected producer,
Simple test, native compile or executable was run in this fresh lane.
Runtime reproduction/fix cycles used: **0 of 6**. Qualification remains pending.
