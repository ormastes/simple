# Borrow check: "spurious errors on trivial code" REFUTED; two fail-opens found instead

**Date:** 2026-08-08
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Area:** `src/compiler/55.borrow/borrow_check/`, `src/compiler/80.driver/`

## Summary

The open finding claimed the borrow checker **emits errors on trivial code that
should produce none**, inferred from `nll.check()` returning falsey during a
Stage-3 SIGSEGV investigation.

**That inference is wrong.** The borrow checker is clean on trivial code. The
falsey return has a different, fully sufficient explanation: the driver's
`borrow_check()` does not report *borrow* errors at all — it reports the
*whole context's* accumulated error count from every prior phase.

## Evidence — the checker is clean

Oracle: `bin/simple test` on the hand-built-MIR borrow specs. Engine: seed-hosted
harness interpreting the pure-Simple `src/compiler/55.borrow/**` sources.

| spec | declared | executed | passed | failed | dropped |
|---|---|---|---|---|---|
| `test/01_unit/compiler/borrow/borrow_check_spec.spl` | 11 | 11 | 11 | 0 | 0 |
| `test/01_unit/compiler/semantics/borrow_check_spec.spl` | 1 | 1 | 1 | 0 | 0 |
| `test/01_unit/compiler/semantics/borrow_check_conflict_spec.spl` | 21 | 21 | 21 | 0 | 0 |
| `test/feature/usage/borrowing_spec.spl` | 4 | 4 | 4 | 0 | 0 |
| `test/01_unit/compiler/borrow/lifetime_spec.spl` | 15 | 15 | 15 | 0 | 0 |

52/52, `dropped=0`. **Evidence weight is not uniform across these rows.** Only
row 1 (`borrow_check_spec.spl`, 11 cases) is sabotage-verified live against
`55.borrow` — see below. The other four rows are corroboration of unverified
depth; `borrowing_spec.spl` in particular is a feature spec that may not reach
`55.borrow` at all. The conclusion rests on row 1, which is sufficient on its own
because it contains the negative controls.

`borrow_check_spec.spl` carries **both polarities** — four
negative controls that must NOT flag (`accepts plain copies with no move
involved`, `does not flag use of a different local after a move`, `accepts use of
the source after re-initialization`, `accepts returning a different local after a
move`) alongside positive use-after-move cases. The negative controls are exactly
the "trivial code that should produce no errors" question, and they pass.

### Liveness proof (the oracle is not stale)

A pass is only meaningful if the spec runs the real source. Sabotage: appended an
unconditional `NLLError(message: "SABOTAGE-MARKER-XYZ", ...)` push immediately
before `return self.errors.is_empty()` in `nll.spl` (`NLLChecker.check`).

Result: `passed=7 failed=4 dropped=0` — **precisely the four negative controls
flipped**, positives unaffected. This proves the spec executes
`src/compiler/55.borrow/borrow_check/nll.spl` as source and that an error
injected there is observable.

File restored and verified by content diff (not `git checkout` — that restored a
file to the empty blob in another lane today). All five borrow sources verified
byte-identical to `origin/main`:

```
nll.spl          5959c25a823175dea89ebe3ee79ae2aa65975351
mod.spl          fdc1507a9e5b84f998d14e90064a16b305588325
borrow_graph.spl 8e13a162e3f9287230367417ff90edb5013133aa
lifetime.spl     e7ffab81fbcb1d1a9699878fc05ca8ddde37190e
__init__.spl     2a30576e3fd8c9e887c7d26a0fdc37a97a104446
```

## Root cause of the wrong inference

`src/compiler/80.driver/driver_pipeline_passes.spl:11`:

```
me borrow_check() -> bool:
    if self.ctx.options.no_borrow_check: ...
    for name in self.ctx.mir_modules.keys():
        val errors = check_mir_module(self.ctx.mir_modules[name])
        for err in errors:
            self.ctx.add_error(_format_nll_error(err))
    self.ctx.errors.len() == 0          # <-- WHOLE-CONTEXT count
```

The return value is `ctx.errors.len() == 0`, not "zero NLL errors". Any error
accumulated by source loading, parsing, HIR/resolution, monomorphization or MIR
lowering makes `borrow_check()` return false **with zero borrow errors present**.

This directly explains the Stage-3 observation without any borrow-checker defect,
and it is amplified by the known `MirLowering.errors` collection: those errors are
already in `ctx` by the time borrow check runs.

## Fail-open #1 — prior-phase errors are misreported as BorrowError

`driver_aot_pipeline.spl:97`:

```
if not self.borrow_check():
    for err in self.ctx.errors: log_error("Borrow error: {err}")
    return CompileResult.BorrowError(self.ctx.errors)
```

Every prior-phase error is relabelled `Borrow error:` and returned as
`CompileResult.BorrowError`. This is a **diagnostic misattribution**: it sends
investigators to `src/compiler/55.borrow/` for defects that live in lowering or
resolution. It cost this lane's predecessor exactly that detour.

**Deliberately NOT fixed here.** Making `borrow_check()` count only NLL errors
would suppress genuine prior-phase failures and manufacture a *fourth* fail-open
in a pipeline that already has three. The correct fix is to keep the gate but
separate the *label*: report borrow errors and pre-existing context errors
distinctly. Filed rather than drive-by patched.

## Fail-open #2 — borrow check is skipped in Stage 2 and Stage 3 (not Stage 4)

`driver_aot_pipeline.spl:93`:

```
val bootstrap_flat_aot = (rt_env_get("SIMPLE_BOOTSTRAP") ?? "") == "1"
    and (rt_env_get("SIMPLE_BOOTSTRAP_STAGE4") ?? "") != "1"
if bootstrap_flat_aot:
    log_phase("aot:flat_mir_passes:skipped")
else:
    ... borrow_check / process_async / optimize_mir ...
```

Under `SIMPLE_BOOTSTRAP=1` without `STAGE4=1`, borrow check (and async processing
and MIR optimization) never run.

Which stages land on which side, traced in `scripts/bootstrap/bootstrap-from-scratch.sh`:

- `SIMPLE_BOOTSTRAP_STAGE4=1` is set at **exactly one** site, line 827, inside
  `bootstrap_native_build_main()` (defined line 807).
- That function is called **once**, at line 1925, as
  `run_logged stage4-native-build bootstrap_native_build_main` — **Stage 4 only**.
- Line 1231 does a global `export SIMPLE_BOOTSTRAP=1` with **no** `STAGE4`. The
  Stage-2 and Stage-3 native-build invocations (≈ lines 1523, 1635, 1817) inherit
  that export.

So: **Stage 4 borrow-checks; Stage 2 and Stage 3 do not.** Any claim of the form
"Stage 3 passed borrow check" is vacuous under the standard bootstrap script.

This also reconciles the prior Stage-3 observations that *did* reach the borrow
checker: those runs set `STAGE4=1` explicitly (e.g.
`scripts/check/check-stage4-selfhost-parse-memory-multifile.shs:235` sets
`SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE4=1`), which flips `bootstrap_flat_aot`
false and re-enables the block. Whether borrow check runs at all is therefore
environment-dependent, which is itself the hazard.

## Fail-open #3 (observed) — `load_sources_impl()` returns true with zero sources

A driver-level probe with `options.input_files` set to an **absolute** path ran
the full phase sequence — load, parse, HIR, mono, MIR — with every phase
returning `true`, and produced `sources=0`, `hir_modules=0`, `mir_modules=0`.
`borrow_check()` then returned `true` **vacuously**, having iterated an empty
dict. Switching to a repo-relative path made phase 1 do real work (and exceed a
40-minute interpreted budget).

**Cause not isolated.** Only one variable was changed (absolute → relative), and
the relative-path run was abandoned at a 40-minute interpreted-mode budget rather
than completing, so the comparison is one-sided. The input file *did* exist at
the absolute path used (confirmed by a later successful `mv` of it). The
observation is consistent with the recorded trap "absolute-path `simple compile`
exits 0 without compiling", but this evidence does not establish that mechanism —
it is a lead, not a conclusion.

What *is* established regardless of cause: a zero-module pipeline reported
success at every phase, and `borrow_check()` returned true having checked
nothing. That is how a "borrow check passed" claim can be produced without a
single function being checked, and it is the failure mode to control for when
someone next reports borrow check as green.

## Still-latent, NOT addressed here

The `NLLChecker.errors` field-offset defect (consumer in `mod.spl:77`
`val errors = nll.errors` reading at 0x58 where `nll.spl` reads 0x20 internally)
is real and unfixed. It is a codegen/field-index defect, a separate lane from
this question. It is only *reachable* when `nll.check()` returns falsey — which,
per the above, is driven by prior-phase errors, not by borrow violations.

## Pipelines that actually call borrow check

Counted by call, not keyword — three pipeline call sites, all live:

| call site | enclosing entry point |
|---|---|
| `driver_aot_pipeline.spl:97` | `me aot_compile()` (AOT) |
| `driver_pipeline_execution.spl:21` | `me jit_compile_and_run()` (JIT) |
| `driver_orchestration.spl:238` | `me compile_vhdl_only()` (VHDL) |

Plus `src/app/compile/test_dc_leak.spl:66`, a harness, not a pipeline.

## Bottom line

Borrow check is **not** a third false-signal source in the Stage-3 pipeline. It
is clean on trivial code. It is, however, *silently skipped in Stages 2 and 3*
(enabled only by `SIMPLE_BOOTSTRAP_STAGE4=1`) and *credited with other phases'
errors* when it does run — so neither a green nor a red from `borrow_check()`
currently means what its name implies.

Practical consequence for the Stage-3 investigation: a falsey `borrow_check()`
is **not** evidence of a borrow violation. Before attributing anything to
`55.borrow`, read `ctx.errors` and check whether the entries are borrow errors at
all — under the current code they usually are not.

## Re-verification 2026-08-17 (fleet lane C, by CONTENT)

The doc's own framing holds. `src/compiler/55.borrow/borrow_check/nll.spl:363` still reads
`return self.errors.is_empty()` — intact, so the refuted primary spurious-error claim stays
refuted. A grep for `fail_open`/`fail.open` across `src/compiler/55.borrow/` returns NOTHING,
so the two secondary driver fail-opens are not marked in source and could not be located by
name; they remain open and unlocated.

UNPROVEN: the two secondary fail-opens. They are described only in prose here, have no
in-source marker, and `test/01_unit/compiler/borrow/borrow_check_spec.spl` does not target
them. Someone must first pin them to a `file:line` before they can be fixed or closed.
