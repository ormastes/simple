# MIR transient scope frees unpromoted `rti` rows: E-MIR-TYPE-Transport / E-RTI-003 / access violation (2026-11-01)

## Symptom
A stage2 built from `release/1.0.0` at or after `33bba69184f` (#5709, "compiler:
bound MIR setup transient scopes") fails `native-build --entry-closure` on an
entry that pulls `lib.nogc_async_mut.fiber.io_reactor` / `lib.nogc_sync_mut.io.time_ops`
/ `compiler.frontend.*` (lane repro `test/p3_e0_repro/repro_io.spl`):

- `E-MIR-TYPE-Transport: invalid HirType kind carrier observed at MIR boundary
  owner=sleep_ms context=body ... caller_disc=-2 relation=already-invalid-at-caller`
  (also owners `fiber_io_close`, `frontend_parse_or_restore`,
  `parser_variant_named_dependencies`, `frontend_spab_load_v1`)
- `E-RTI-003: unsubstituted generic parameter in 'n:lib.nogc_async_mut.async.poll:...[p0]'
  reached a concrete consumer` (5x in `lib.nogc_async_mut.async.future`)
- `ICE[mir_lower] module compiler.frontend.core.parser: worker died inside this
  module (worker exit status -1073741819)` = 0xC0000005 access violation.

A stage2 built from the same sources minus #5709 (`2c7305bbbbb`, E0 branch on
`7c7444b8682`) lowers all 282 closure modules through MIR (`phase=mir done=282
succeeded=282 failed=0`). The pinned phase-3 stage2 (`ef0681fc0e1`) also lacks
#5709 and does not show the failure.

## Root cause
`MirLowering.rti: ReturnTypeInterfaceTable` was added by RTI PR1
(`d0e58600707`, 2026-10-27) two days after `promote_transient_owner`
(`src/compiler/50.mir/_MirLowering/transient_owner.spl`, last reconciled
`ed2581b83d3`, 2026-10-25) enumerated every `MirLowering` field as a
promotion root. Three more fields were likewise never added:
`rti_last_error`, `runtime_value_extern_abis`, and E0's
`erased_callback_record_bindings` (#5732).

#5709 (`src/compiler/80.driver/driver_pipeline_lowering.spl`) wraps
`prescan_module_struct_names` in `transient_array_scope_begin_v1()` /
`_driver_mir_inventory_scope_end`. That prescan calls
`prescan_module_functions_v1`, which registers `ReturnTypeRow`s into
`self.rti.register_rows(...)` (`module_lowering.spl:1954`). The rows are
allocated inside the scope; `promote_transient_owner` never retags `self.rti`,
so `transient_array_scope_end_v1()` frees them. Every later consumer reads the
dangling rows: when the freed memory still looks like an enum the
`_sffi_hir_type_discriminant` probe reports an invalid carrier
(E-MIR-TYPE-Transport, E-RTI-003); when it has been reused, the read is an
access violation. It is a use-after-free, not a type error, which is why it
surfaces as an AV instead of a diagnostic.

E0 (#5732) is not the cause: the E0-branch compiler without #5709 passes, and
the failing owners (`sleep_ms`, `fiber_io_close`) contain no generics.

## Fix
`promote_transient_owner` promotes `rti`, `rti_last_error`,
`runtime_value_extern_abis`, `erased_callback_record_bindings`.
Regression gate: `test/01_unit/compiler/mir/transient_owner_promotes_every_field_spec.spl`
asserts every `struct MirLowering` field is a `promote_and_release_transient_owner_roots`
root, so a new field can no longer be silently freed by a scope.

## Phase 3
Run 13 may rebase onto #5732 (E0); it must include this fix (or exclude #5709)
or MIR lowering dies on the first scoped prescan.

## Run 3 verification (2026-11-05): still failing — the rti roots were not the (only) leak

Sanctioned bootstrap run 3 (`release/1.0.0` `a6174dbdbe9`, includes `d05dc7079db`
rti-children roots and #6740) admitted Stage 2 (`6bb69e9220400c15`, aarch64) and
its compiler tests failed in MIR
(`build/bootstrap-opus-3/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/`):

- `test_runner_build`: 2 real module failures (`app.test_incremental_state_shared`
  owner=`save`; `lib.nogc_sync_mut.io.debug_stubs` owners `rt_debug_pause_exec`,
  `rt_debug_set_breakpoint_enabled`, `rt_debug_set_step_mode_val`,
  `rt_debug_terminate`, all `context=body param_index=-1 caller_disc=-2
  relation=already-invalid-at-caller`) sealed both shards, which is why the
  aggregate reports 319 failed modules. Plus `unresolved method call: reverse`
  (`lib/nogc_sync_mut/spec/dir_prevention.spl:94`, separate — see below).
- Every failing owner (here and in the 11-01 record: `sleep_ms`,
  `fiber_io_close`, `main` in the repro) has a **symbol-free return type**
  (implicit unit / bool / i64) and is called **cross-module**. That is the
  population `bootstrap_fn_ret_hir_type_register` accepts
  (`hir_type_metadata_symbol_free`) and `bootstrap_fn_ret_hir_type_lookup`
  answers from the body path (`switch_operators_calls.spl:2141` /`:2184` ->
  `lower_type(reg_ret_ty)`), not the rti table (rti is consulted only for enum
  match subjects, `rti_enum_match_subject_type`).

### Reproduction (36 s, peak RSS 1.1 GB, admitted Stage 2, read-only)

```
S2=build/bootstrap-opus-3/stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple   # sha256 6bb69e92…
cat > dbg_entry.spl <<'E'
use lib.nogc_sync_mut.io.debug_stubs.{rt_debug_pause_exec, rt_debug_terminate}
fn main() -> i64:
    rt_debug_pause_exec()
    rt_debug_terminate()
    0
E
SIMPLE_SHARD_MEM_CLAMP=1 systemd-run --user --scope -p MemoryMax=30G \
  $S2 native-build dbg_entry.spl --backend=cranelift --low-memory --threads 1 -o dbg_out
# -> [mir-type-invariant] receipt=1/16 owner=main context=body ... caller_disc=-2
#    (SIMPLE_MIRB_TRACE=1: fires inside stmt=0 of main, the call rt_debug_pause_exec())
# -> MIR lowering error: E-MIR-TYPE-Transport ... owner=main / rt_debug_* (51/53 modules pass)
# SIMPLE_MIR_TAG_PROBE=1 or SIMPLE_TRANSIENT_PROMOTE_DEBUG=1 runs SEGV instead (freed memory reused);
# promote-debug printed 0 refused roots: promotion "succeeded" on the wrong objects.
```

### Root cause (file:line)

`src/compiler/50.mir/mir_data.spl:2525-2542` (`bootstrap_fn_ret_hir_type_register`)
and `:2494-2499` (`bootstrap_fn_ret_type_register`). Both store a plain value
struct (`HirType` / `MirType`) in a cross-module registry dictionary and then
journal the **parameter** `ty` for delta promotion (`_bootstrap_fn_delta_hir_type(ty)`
/ `_bootstrap_fn_delta_mir_type(ty)`). On the native path every non-`mut`
by-value struct parameter gets the Bug #167 prologue copy
(`_MirLowering/function_lowering.spl:732-736`, `copy_struct_value_recursive`),
so the journal held a *different* in-scope copy than the dictionary. The first
promotion in a process adopts every registry wholesale (`_bootstrap_fn_registries_adopted`),
which is why rows from the first prescanned module survive; every later module's
rows were freed at `transient_array_scope_end_v1()` and read dangling by the next
cross-module call. Same class as `doc/bug_report/mir_hir_registry_ambiguity_copy_2026-10-26.md`
(text keys) and `transient_promote_struct_param_copy_dangles_2026-10-25.md`
(promote wrapper), one layer down. The rti roots added on 11-01/11-02 were
correct but did not cover this registry.

### Native proof of the mechanism (same admitted Stage 2, no rebuild)

Three single-variant probes (`Dict<i64, Row>` + journal `[Row]`, two scopes —
adopt-whole then delta-only — then a reuse scope), compiled by the admitted
Stage 2 and run:

| variant | shape | delta-scope rows dangling |
|---|---|---|
| A | journal the by-value `row` parameter (= mir_data.spl before) | **16/16** |
| B | `mut row` / `mut value` params (no prologue copy) | 0/16 |
| C | journal `reg[key]` read back after the set | 0/16 |

(adopt-scope rows: 0/16 in all three; `scopes_ok=true` in all three.)
A first, text-keyed version of the same probe SEGV'd in all three variants in
the second scope, inside the register function's text-parameter prologue
(`rt_string_new_uncached_impl` dereferencing the key bytes "delta.0" as a
pointer) before any struct-copy effect could show; it was sidestepped with
integer keys and is not explained here (likely the text-param copy class of
`stage2_transient_promote_text_param_copy_2026-11-03.md`).
A fixture importing the real `compiler.mir.mir_data` could not be compiled by
the admitted Stage 2 at all: its own `register_module` (calls the unit-returning
`bootstrap_fn_ret_hir_type_register` cross-module) tripped the same
`E-MIR-TYPE-Transport caller_disc=-2`, then SEGV — a third independent repro of
the compiler-side symptom, and the reason the real-registry confirmation needs
the rebuilt Stage 2.

### Fix (this change)

- `mir_data.spl`: `_bootstrap_fn_delta_stored_mir_type(name)` /
  `_bootstrap_fn_delta_stored_hir_type(name)` journal the dictionary's own
  stored value (`registry[name]`, variant C — robust against any upstream copy),
  replacing the two by-value helpers. No new allocation: the journal entry count
  is unchanged (one row per registration), promotion stays delta-sized (the
  scaling example of `bootstrap_fn_registry_delta_promote_spec` still passes).
- `_MirLowering/transient_owner.spl`: `symbol_write_ledger` (8c2d517fdfa)
  added as a root; `transient_owner_promotes_every_field_spec` was 5/6 on the
  baseline for exactly this field, 6/6 now.
- `test/01_unit/compiler/mir/bootstrap_fn_registry_delta_promote_spec.spl`:
  the journal gate accepts the stored-value journal, and a new source-shape
  example pins that the two struct journals push `registry[...]`, never a
  parameter (the interpreter cannot observe the prologue copy, so the gate is
  static). Pre-existing, unchanged: "journals every registry write" still
  reports the 20 `replace:` offenders in the reset block (`mir_data.spl:2941-2960`)
  on baseline and after.

Seed-interpreter specs (`/home/yoon/dev/cargo-rel100/simple-ref test`, regression
gates only — the seed emits no prologue copy, so they could not reproduce):
`transient_promote_struct_root_spec` 3/3, `transient_promote_text_param_spec` 2/2,
`rti_unsubstituted_generic_fallthrough_spec` 5/5, `bootstrap_fn_registry_delta_promote_spec`
4/5 (new example passes; the pre-existing failure above), `transient_owner_promotes_every_field_spec` 6/6.

### What still needs the bootstrap re-run

The compiler-side symptom (`dbg_entry` repro above, the stage2 compiler tests)
can only turn green on a Stage 2 rebuilt from this source: the registry code
is baked into the admitted binary. Re-verify with the sanctioned lane
(`scripts/bootstrap/bootstrap-from-scratch.sh`, see `.claude/rules/bootstrap.md`)
from a tree containing this commit, then re-run the `dbg_entry` repro with the
new `stage2-admitted/simple` (expect `phase=mir ... failed=0`, no
`[mir-type-invariant]` line) and read
`stage2-compiler-tests/.../verification/summary.env` for `task=test_runner_build|result=PASS`.
Peak RSS to compare: run 3 `test_runner_build` max_rss 2,543,412 KiB,
`compiler_cli_build` 18,383,080 KiB (`logs/*.max-rss-kib`); the fix adds no
allocation and removes none, so a material change in either is a regression to chase.

### The other three symptoms of run 3

- `unresolved method call: reverse` (`dir_prevention.spl:94`, `found.reverse()` on
  a `[text]` local): **separate, fixed here.** A 10-line standalone probe fails
  identically on the admitted Stage 2 (no scope involved). The unresolved-array
  branch in `_MirLoweringExpr/method_calls_literals.spl:5174` only knew `clear`
  / `sort`; `reverse` now routes to `rt_reverse_mut` (in place, returns the
  receiver — same ABI shape as `rt_sort`). `rt_reverse_mut` is exported by the
  run-3 runtime capsule (`phase2-runtime-capsules/6bb69e92…/libsimple_native_all.a`:
  one `T rt_reverse_mut`, next to `T rt_sort`). Would have kept
  `test_runner_build` red after the registry fix. The lowering itself is
  baked into Stage 2, so the standalone probe can only be re-run on the
  rebuilt binary (seed-interpreted `bootstrap_main.spl native-build` attempt:
  see the commit report).
- `[mir-lower] WARNING: struct/class name 'JoinPoint' re-registered with a
  DIFFERENT field list ... keeping EXISTING`: separate, pre-existing bare-name
  collision class (two unrelated `JoinPoint` structs in the closure; the log
  shows the same for `TestStats`, `TestResult`, `WalEntry`, `Event`, ...). Warning
  only; not a cause of the shard failure. Not fixed; tracked by the bare-name
  field-index ambiguity note the warning itself cites.
- `compiler_cli_build` `[mir-shard] owner=0/2@0 status=BLOCKED exit=-2 claimed=0
  ... blocked=worker could not be reaped`: separate from the UAF as far as the
  log shows. Timeline (`compiler_cli_build.log`): `mir_setup:struct_prescan`
  966 s -> 981 s, `mir_setup:enum_inventory` 981 s -> 1535 s with progress rows
  at `dt_ms=545085` and `569141`, then both shards BLOCKED having claimed 0
  modules (`native_internal_timeout_seconds=1800`). The per-module
  `transient_array_scope_begin_v1` -> `register_module_enum_inventory_v1([one
  module])` -> `promote_transient_owner()` (every MirLowering root) loop in
  `driver_pipeline_lowering.spl:1244-1250` is walked 3,006 times for this
  closure, i.e. a whole-lowering promotion per module. Unconfirmed whether the
  workers died (no worker crash line in the campaign logs) or timed out;
  recorded, not fixed.
