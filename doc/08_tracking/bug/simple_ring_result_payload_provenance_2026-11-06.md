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
