# `simple check` accepts type-invalid programs

- **Status:** OPEN — live false-green reproduced on the deployed CLI and standalone worker
- **Observed:** `fn main(): val x: i64 = "text"` exits `0` with `All checks passed` through both `simple check` and `simple run src/app/check/main.spl`.
- **Cause:** both pure-Simple check workers stop after parsing plus source-policy rules. The canonical `CompileMode.Check` reaches HIR lowering, but general HM diagnostics remain opt-in warnings and never enter compiler errors.
- **Stale plan:** `doc/03_plan/cert/redeploy_kit/typecheck_fatal_enablement.md` says Phase A fatal wiring exists, but current `src/compiler` contains no `SIMPLE_TYPECHECK_FATAL` or `run_typecheck_fatal_pass` owner.
- **2026-07-19 bounded repair evidence:** two source-compatibility blockers in the canonical path were fixed: `TraceConfig` now uses implicit field receivers, and `HmInferContext.subsume` propagates `Result` with an explicit match instead of unsupported enum `.map(())`. The warn-only canonical command then completed and emitted one HM diagnostic for the negative corpus; `bidir_type_check_spec.spl` locks both source forms (3 examples, 0 failures).
- **HM tail-value repair:** `HmInferContext.infer_block` now infers the lowered `HirBlock.value` when `block.has` instead of returning the last statement type (or `Unit`). Four source regressions cover a valid typed tail, a mismatched typed tail, a discarded Unit-body value, and an annotated local mismatch (4 examples, 0 failures).
- **Remaining fatal-enable blocker:** explicit `return` lowers to `HirExprKind.Return`, which HM expression inference does not yet handle. Add expected-return context and termination-aware flow before making HM fatal for the broader source corpus.
- **Root solution:** support explicit returns, prove the paired reject/positive CLI corpus, then make HM fatal only in `CompileMode.Check` and route both workers through the canonical internal owner. A second pattern-based checker would preserve divergence.
- **Existing contradiction:** `test/02_integration/app/diagnostics/check_diagnostics_contract_spec.spl` already expects the mismatch to fail; its prior green status is not current runtime evidence.

## Re-check 2026-09-12 — the reported false-green is not reproducible

Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` sha256 `3d120a6f`

The record's headline case — `fn main(): val x: i64 = "text"` exiting `0` with
`All checks passed` — no longer happens. It is now rejected, with a semantic
diagnostic and a non-zero exit:

```
$ SIMPLE_RUST_SEED_WARNING=0 bin/simple check d_check.spl; echo $?
d_check.spl:2:18: error[semantic]: type mismatch: expected HirTypeKind::Str, found HirTypeKind::Int((64, true))
1 error(s) found in 1 of 1 file(s)
1
```

So HM diagnostics do reach compiler errors on this shape, and the "Remaining
fatal-enable blocker" framing above is stale for at least the annotated-local
mismatch. (The diagnostic's own wording has expected/found inverted — it says
`expected Str, found Int` for `val x: i64 = "text"` — which is cosmetic but
misleading; not filed separately.)

One caveat found in the same pass, filed separately rather than left implicit:
`simple check` on a CLEAN file exits 1 with zero output, i.e. the error path works
but the success path does not. See
`doc/08_tracking/bug/simple_check_clean_file_exits_1_with_no_output_2026-09-12.md`.
That is a false RED, the opposite failure mode from the false GREEN reported here,
and it does not resurrect this bug.

- Status: CLOSED (2026-09-12) — not reproducible on 3d120a6f
