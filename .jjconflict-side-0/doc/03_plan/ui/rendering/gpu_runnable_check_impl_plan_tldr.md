# GPU-Runnable Check Plan — TLDR

Full plan: `gpu_runnable_check_impl_plan.md` · Design: `doc/05_design/ui/rendering/gpu_runnable_check_design.md`

Baseline: scanner prototype (`src/app/gpu_lint/gpu_runnable_scan.spl`) reports
46% of engine2d+browser_engine fn names blocked; top blockers string-op,
list-push, interpolation, recursion-cycle (mostly name-merge artifacts),
closures; `webgpu_sffi_`/`metal_sffi_` blocks are whitelist-calibration bugs.

- **Stage 1 — scanner productionization (no compiler change):** whitelist
  `webgpu_sffi_`/`metal_sffi_` (`gpu_runnable_scan.spl:113-116`), cheap
  receiver-aware call matching (self-calls → same file, skip trait sigs),
  new `scripts/check/check-gpu-runnable.shs` gate in warning mode + pre-commit.
- **Stage 2 — `@gpu_runnable` + 35.semantics fixpoint pass:** one parser elif
  (`enum_module_body.spl:668`), flat-AST slot, `HirFunction` bool, pass after
  HIR merge wiring the dead `gpu_checker.spl` ban list + `alloc_inference`
  fixpoint + SCC recursion; name+arity overload table (all-must-pass);
  call-chain diagnostics; editor surfacing via `query_lint`.
- **Stage 3 — renderer waves:** W1 engine2d primitives — AOP split into
  gpu-runnable core + CPU shell (shell owns print/format/push/budget);
  W2 DrawIR exec + tile checksums, promote `SIMPLE_WEB_TILE_GPU` lane;
  W3 wire the orphaned gpu_web CUDA layout port
  (`cuda_execution_port.spl:389-433`) behind a flag, consume
  `LayoutExecutionProof.reason`.
- **Exit:** scanner gate ratchets; Stage-2 pass error-mode on marked roots.
