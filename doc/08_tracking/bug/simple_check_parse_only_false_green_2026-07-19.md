# `simple check` accepts type-invalid programs

- **Status:** OPEN — live false-green reproduced on the deployed CLI and standalone worker
- **Observed:** `fn main(): val x: i64 = "text"` exits `0` with `All checks passed` through both `simple check` and `simple run src/app/check/main.spl`.
- **Cause:** both pure-Simple check workers stop after parsing plus source-policy rules. The canonical `CompileMode.Check` reaches HIR lowering, but general HM diagnostics remain opt-in warnings and never enter compiler errors.
- **Stale plan:** `doc/03_plan/cert/redeploy_kit/typecheck_fatal_enablement.md` says Phase A fatal wiring exists, but current `src/compiler` contains no `SIMPLE_TYPECHECK_FATAL` or `run_typecheck_fatal_pass` owner.
- **Root solution:** restore the planned fatal HM pass behind its blast-radius gate, prove reject/positive corpora, then route both check workers through canonical `check_file`. A second pattern-based checker would preserve divergence.
- **Existing contradiction:** `test/02_integration/app/diagnostics/check_diagnostics_contract_spec.spl` already expects the mismatch to fail; its prior green status is not current runtime evidence.
