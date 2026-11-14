# Stage 2 compiler-test matrix rejected on pin 18a1f28937c2 (Windows GNU)

Date: 2026-11-14 · Severity: P1 · Status: open

Evidence root (V): `<lane>/build/bootstrap/pinned-src/pinned-18a1f28937c2/
.simple/storage/build/bootstrap/stage2-compiler-tests/x86_64-pc-windows-gnu`
(`rejection.env`, `verification/summary.env`, `verification/logs/*`).
Phase 2 admission PASSED; the mandatory matrix rejected
(`terminal_failures=6`), so `--resume-managed-from-admitted` refuses with
"compiler-test PASS receipt unavailable"
(`scripts/bootstrap/lib/verify-stage2-compiler-tests.shs:191`).

## Row disposition

| row | result | cause |
|---|---|---|
| compiler_cli_build | FAIL status=1, 6018 s | HIR shard worker exited 1: `[hir-cache-store] refused ... unencodable HirTypeKind enum module=src/compiler/80.driver/watcher/watcher_client.spl` then `E-HIR-VISIT-UNHANDLED: HirTypeKind variant <unknown> unhandled at walk_hir_type` (last line of `compiler_cli_build.log`, line 45950, at 2757/3147). Not killed/OOM: 6018 s is far below the 28800 s campaign timeout and the worker printed its own fatal diagnostic. Tracked as `candidate_hir_typekind_escapes_codec_visitor_2026-11-14`; root-caused and fixed by PR #9056 (`aa97b033f81`, `hir_lambda_param_hint_outlives_module_scope_2026-11-14`: `lambda_param_hint` survived `begin_module`), which is NOT in `18a1f28937c2`. |
| test_runner_build | FAIL status=1, 8331 s | link succeeded, then `native no-op receipt publication failed: output-missing` (`test_runner_build.log:5146`). `native_noop_receipt_misses_windows_exe_suffix_2026-11-14`. |
| compiler_bootstrap_tests, interpreter_interpreter_tests, loader_interpreter_tests | UNSUPPORTED `full-cli-artifact-not-built` | dependents only: they need the `compiler_cli_build` artifact and never ran. |

Both real failures execute inside the admitted Stage 2 binary, so
`admit-built-stage2-compiler-tests.shs` against the same Stage 2 cannot pass;
a PASS matrix needs a new pin carrying both fixes.

## Proposed workaround (NOT executed)

Proposed 2026-11-14 and cancelled by the owner the same day (the lead builds
Phase 3 directly from the admitted Stage 2). Nothing below has been run; the
commands are unverified, including the claim that the Stage 3 planner receipt
is written before the matrix step.
The legacy Stage 3 lane (`--resume-stage3-from-admitted`) does not consume
the compiler-test receipt; it needs a `//bootstrap:stage3` planner receipt,
produced by `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`
against the admitted Stage 2 (typed reason `verify-landed-compiler-fix`).
The matrix `rejection.env` stays in place, so the managed Phase 3/4 path
remains refused and nothing is reported as a matrix PASS. No gate, row or
receipt check is changed. Superseded once a re-pinned lane
publishes `stage2-compiler-tests.env` with `status=pass`.

### Commands (run from the pinned source root; one native build at a time)

```sh
P=/c/dev/wt-lane2/build/bootstrap/pinned-src/pinned-18a1f28937c2
O=$P/.simple/storage/build/bootstrap
cd "$P"
# LLVM: Stage 3 from the admitted LLVM Stage 2
SIMPLE_BOOTSTRAP_EXTERNAL_OUTPUT_ROOT=$O sh scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs \
  --target=//bootstrap:stage3 --reason=verify-landed-compiler-fix --planner-backend=llvm \
  --parent-compiler=$O/stage2/x86_64-pc-windows-gnu/simple.exe \
  --bootstrap-output=$O --out=$O/stage3-planner-admission.receipt
sh scripts/bootstrap/bootstrap-windows.sh --resume-stage3-from-admitted=$O \
  --bootstrap-receipt=$O/stage3-planner-admission.receipt --jobs=1
```

Stage 3 resume takes its backend from the Stage 2 transcript, so Cranelift
needs its own Stage 2: run the lane with `--backend=cranelift
--produce-stage3-receipt=verify-landed-compiler-fix` (separate output root).
The planner receipt is produced BEFORE the matrix step, so it still exists
when the matrix rejects again; then resume Stage 3 the same way.
