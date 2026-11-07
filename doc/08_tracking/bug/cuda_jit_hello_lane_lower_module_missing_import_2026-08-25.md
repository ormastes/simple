# cuda_jit hello lane: `lower_module` not found, then seed interpreter method collision (2026-08-25)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** fix-implemented-verification-pending (2026-11-07, #7498): symptom 2 (same-name type collision) fixed in the seed interpreter by the module-qualified type registry; verify on the CUDA host with `bin/simple test test/03_system/gpu_lane/cuda_jit_hello_spec.spl` (expect no `ParserModule has no field named friends`). Import half fixed earlier.
**Spec:** `test/03_system/gpu_lane/cuda_jit_hello_spec.spl` — `Results: 14 total, 13 passed, 1 failed`
on `bin/simple` = Rust seed, host with 2 live CUDA devices (`SIMPLE_GPU_TEST=1 SIMPLE_CUDA_TEST=1`).
Sibling `vulkan_jit_hello_spec.spl` passes live on the same host (`2 total, 2 passed`).

## Symptom 1 — FIXED
`semantic: method lower_module not found on type HirLowering`.
`src/lib/gc_async_mut/gpu_lane/cuda_jit_lane_executor.spl` imported only
`compiler.hir.hir_lowering.types.{HirLowering}`; the `impl HirLowering` extension block that
defines `lower_module` lives in `compiler.hir.hir_lowering.items` (see
`src/compiler/20.hir/hir_lowering/__init__.spl:28-36`). `MirLowering` was likewise used without an
import. Fix: add `use compiler.hir.hir_lowering.items.*` and
`use compiler.mir.mir_lowering.{MirLowering}` — exactly what the canonical
`test/02_integration/rendering/cuda_compiler_ptx_live_spec.spl:9-12` imports.

## Symptom 2 — OPEN (seed interpreter, not this lane)
With the import in place the lane now reaches `lower_module` and returns
`cuda-jit-hir-lowering-failed`. A minimal spec that only parses
`vector_add_kernel_source()` and calls `HirLowering.lower_module` fails with
`semantic: class ParserModule has no field named friends`. `friends` is a field of the
visibility class in `src/compiler/00.common/dependency/visibility.spl:258-266`
(`is_friend`); the seed interpreter resolves class members by NAME across co-compiled modules
(the documented `compiler_cross_module_private_symbol_collision` class), so a same-named member
lookup lands on the wrong class. Which collision fires depends on the import set — the live PTX
spec (different import set) gets past lowering and fails later with `expected 1 to equal 0`.

Reproduce: `bin/simple test <spec with the 6 imports of cuda_jit_lane_executor + lower_module call>`.
Unblocks when: a pure-Simple self-hosted `bin/simple` is deployed (the bootstrap redeploy is
tracked separately), or the seed's cross-module member resolution is keyed by class identity.


## 2026-11-07 — seed cross-module class resolution keyed by owner (round 15)

The seed now resolves a bare class name through the using module's own
definitions and imports (`resolve_class_in_scope`), and dispatches an
instance's method against the definition whose fields match the instance
(`resolve_class_for_instance`), instead of the flat last-registration-wins
map; see `engine_specs_spec_runner_interpreter_divergence_2026-09-16.md`
(2026-11-07 note) for the mechanism and the repro/prevention specs. Whether
the `ParserModule has no field named friends` member collision in this lane
is fully covered is reported in the PR table from a re-run of
`test/03_system/gpu_lane/cuda_jit_hello_spec.spl` on the fixed seed.
