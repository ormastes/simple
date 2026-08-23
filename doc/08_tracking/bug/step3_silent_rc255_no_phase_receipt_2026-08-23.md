# Step 3/6 (typecheck + monomorphization) can fail with rc=255 and ZERO output

- **Filed:** 2026-08-23
- **Status:** receipts landed; rc=255 root cause under investigation (see Evidence)
- **Severity:** BLOCKING for stage1 — this is the wall immediately after HIR
- **Source:** phase36 forecast, finding #1 (rated CERTAIN)

## Symptom

```
native-build --source src/app --entry-closure --entry src/app/lint/main.spl
...
[build] hir 140/140 step 2/6 +...ms dt=...ms <module>
<process exits rc=255>
```

No `error:`, no `[mono]` receipt, no `step 3/6` line, no `phase 3 FAILED`.
The failure is not merely hard to diagnose — there is literally nothing to read.

## Root cause of the UNDIAGNOSABILITY (fixed here)

Two separate reporting gaps, both of the same class:

1. **No receipts between `hir N/N step 2/6` and `mir step 4/6`.** The per-module
   HIR loop is the last emitter. Everything after it — `mem_snapshot_finish`,
   the collect-all summary, `driver_validate_value_struct_layouts`, the
   typecheck / safety / any-escape / enum-contract passes, AST reset + source
   reclaim, then all of monomorphization and `post_mono_verify` — emitted no
   `log_build_progress` at all. `log_phase` covers some of it but is env-gated
   and off by default.
2. **The phase-3 error preview was gated on `SIMPLE_BOOTSTRAP_DEBUG=1`.** On the
   default configuration `phase 3 FAILED` printed a bare line with no errors
   attached, and a failure carrying ZERO recorded errors (an internal invariant
   break, not a source error) printed nothing distinguishing at all. Phase 2
   already had exactly this defect and had already been fixed the same way a few
   lines above — the fix was never swept to phases 3 and 4. Class defect.

The same class exists at the step 4 -> 5 boundary: the aot post-MIR pass chain
(`borrow_check`, `process_async`, `optimize_mir`, `weave_aop`) used only
`log_phase`, so a death in any of them was equally mute.

## Fix

Receipts (`log_build_progress`, house style, unconditional — the stdout twin is
not gated on `SIMPLE_BUILD_PROGRESS_EVENTS`) added for:

| step | new phase receipts |
|---|---|
| 2->3 | `hir_finalize`, `post_hir_validate`, `hir_reclaim`, `typecheck`, `safety`, `any_escape`, `enum_contract` |
| 3 | `monomorphize` (start / specialize / terminal), `post_mono_verify` |
| 4->5 | `borrow_check`, `process_async`, `optimize_mir`, `weave_aop`, plus terminal `mir` receipts |

Each emits a start receipt and a terminal receipt (`terminal=failed`, `failed=1`)
on every early return, so the last `[build]` line always names the sub-phase that
died.

Coded diagnostics added, so a non-zero exit always carries a reason:

- `error[E-DRV-PHASE3-000]` — phase 3 returned a failing verdict with zero
  recorded errors (internal invariant break).
- `error[E-DRV-PHASE4-000]` — same for phase 4.
- `error[E-DRV-MONO-001]` — monomorphization refused because phase 3 did not
  admit the build; names the recorded error count and HIR module count.
- The phase-3 error preview is now unconditional (first 20 + a `... N more`
  tail), matching phase 2.

## Files

- `src/compiler/80.driver/driver_hir_pipeline_lowering.spl`
- `src/compiler/80.driver/driver_hir_pipeline_passes.spl`
- `src/compiler/80.driver/driver_aot_pipeline.spl`
- `src/compiler/80.driver/driver_orchestration.spl`
- `test/01_unit/compiler/driver/step3_phase_receipt_contract_spec.spl` (new)
- `test/01_unit/compiler/driver/bootstrap_phase3_error_diagnostics_source_spec.spl` (updated: the gated preview it pinned is the defect)

## Evidence

Reproduce (minutes, not the 72-minute stage1 build):

```
SIMPLE_TIMEOUT_SECONDS=0 SIMPLE_BUILD_PROGRESS_EVENTS=1 \
  <seed> native-build --source src/app --entry-closure \
  --entry src/app/lint/main.spl --threads 4
```

See `EVIDENCE` section appended below for the measured run on the current tree.

## Related

- `ce3c2bf6c71` fix(runtime): retry EINTR-interrupted `rt_process_wait` — a
  DIFFERENT rc=255 in a sibling lane, already on origin. Checked: it is an
  ancestor of the tree measured here.
- phase36 forecast items #2 (E-MONO-033), #3 (generic struct gate), #4
  (`emit_unsupported_panic` fails open) remain open and are NOT addressed here.

## EVIDENCE — measured run 2026-08-23 (receipts landed, rc=255 NOT yet reproduced)

Run: `native-build --source src/app --entry-closure --entry src/app/lint/main.spl
--threads 4`, seed `/mnt/data/worktrees/goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple`,
worktree at `0c085525541`. Log `/mnt/fast/step3/logs/lint_base.log`.

**Result: rc=124 (my own 2400s wall timeout), NOT rc=255.** The build never
reached step 3 in the window: host load average was 46 (other lanes), and parse
alone consumed 620s on the post-shard pass. So the rc=255 root cause is **not
diagnosed** — it is not confirmed as the `ce3c2bf6c71` waitpid-EINTR twin, and
not confirmed as a distinct in-phase abort either. Do not report it as either.

Two things the run DID establish:

1. The receipts are live and correctly ordered on the real pipeline
   (`source_closure 0/1 step 0/6` -> `parse N/140 step 1/6` -> `hir N/140 step
   2/6`), and the HIR shard workers exit via `rt_exit(0)` in `hir_shard_mode`
   BEFORE `hir_finalize`, which is correct — shards are cache-fillers, not the
   real build.
2. **HIR is NOT clean on this tree for the `src/app/lint` closure**, contrary to
   the phase36 forecast's "140/140 clean" (measured on an older tree). This run
   recorded `[hir-fatal]` / `[hir-poisoned]` for at least
   `src/compiler/semantics/lint/_SimdOpportunityLint/byte_checks.spl` (186
   errors) and `.../dispatch.spl` — all `aggregate constructor
   `SimdOpportunity...` is not visible from this module`, the same visibility
   defect class as forecast rung 1 (`ProcessResult` in `process_ops.spl`).
   With errors recorded, phase 3 will now take the *populated* preview branch and
   print them unconditionally, not the `E-DRV-PHASE3-000` zero-error branch.

**Next step for whoever picks this up:** re-run on an unloaded box (or with a
larger `--timeout`); the last `[build]` line will now name the failing
sub-phase, which is precisely what the previous attempt could not produce.
