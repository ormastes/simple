# `simple check` accepts type-invalid programs

- **Status:** OPEN — live false-green reproduced on the deployed CLI and standalone worker
- **Observed:** `fn main(): val x: i64 = "text"` exits `0` with `All checks passed` through both `simple check` and `simple run src/app/check/main.spl`.
- **Cause:** both pure-Simple check workers stop after parsing plus source-policy rules. The canonical `CompileMode.Check` reaches HIR lowering, but general HM diagnostics remain opt-in warnings and never enter compiler errors.
- **Stale plan:** `doc/03_plan/cert/redeploy_kit/typecheck_fatal_enablement.md` says Phase A fatal wiring exists, but current `src/compiler` contains no `SIMPLE_TYPECHECK_FATAL` or `run_typecheck_fatal_pass` owner.
- **2026-07-19 bounded repair evidence:** two source-compatibility blockers in the canonical path were fixed: `TraceConfig` now uses implicit field receivers, and `HmInferContext.subsume` propagates `Result` with an explicit match instead of unsupported enum `.map(())`. The warn-only canonical command then completed and emitted one HM diagnostic for the negative corpus; `bidir_type_check_spec.spl` locks both source forms (3 examples, 0 failures).
- **Fatal-enable blocker:** a paired positive/negative worker experiment made the negative case fail, but also rejected valid `fn answer() -> i64: 42`; JSON reported two files with errors. The fatal/routing experiment was removed after the third verification cycle. HM must first preserve expression-bodied non-Unit return types.
- **Root solution:** fix the HM positive false-positive, prove the paired reject/positive corpus, then make HM fatal only in `CompileMode.Check` and route both workers through the canonical internal owner. A second pattern-based checker would preserve divergence.
- **Existing contradiction:** `test/02_integration/app/diagnostics/check_diagnostics_contract_spec.spl` already expects the mismatch to fail; its prior green status is not current runtime evidence.
