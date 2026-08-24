# Stage 3 self-host SIGSEGV while lowering `values_equal` after full HIR

**Date:** 2026-08-25  
**Status:** FIX IMPLEMENTED — focused regression evidence pending rebuilt compiler
**Platform:** `x86_64-unknown-linux-gnu`, LLVM backend, dynload runtime

## Reproduction

The fresh trust-root run used an isolated jj workspace and a newly rebuilt Rust
seed/runtime. Stage 2 passed compiler sanity plus struct receiver/runtime
capability and was admitted. Stage 3 was then resumed from that immutable
artifact:

```sh
scripts/bootstrap/bootstrap-from-scratch.sh \
  --resume-stage3-from-admitted=build/bootstrap-gpu-r3 --jobs=1 \
  --bootstrap-receipt=build/bootstrap-gpu-r3/planner-admission-stage3.env
```

The wrapper exited 139 (`Segmentation fault (core dumped)`). Evidence is in
`build/bootstrap-gpu-r3/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`.

## Established boundary

- Parse/HIR completed for all **693/693** modules.
- HIR finalization completed **948/948** and post-HIR validation completed
  **693/693**.
- The earlier fabricated `unresolved name: __p-1` diagnostic did not recur.
- MIR lowering reached `src/compiler/backend/backend/interpreter.spl`.
- The last function marker is `lower_function:body-start values_equal`; the
  final expression marker is `block:stmt 0`.
- Immediately beforehand, `resolve_sym_name` completed, but its body emitted
  `WARNING: unresolved method call 'get' lowered to const-0 placeholder
  (silent-null risk, Task #145)`.

This is not the older `n_modules=0` failure: this run retained the complete
module set through HIR and entered real MIR function lowering.

## Focused reproduction and root cause

Two ignored, lane-local fixtures reduced the failure below `values_equal`:
an enum-only match and a single explicit enum match both reach MIR statement 0
and terminate, while an adjacent `if` lowers. The common path copied
`HirMatchArm` composites into a fresh `norm_arms` array and then read
`norm_arms[i].pattern.kind`. The admitted Stage-2 engine erases the pushed
composite element shape at that boundary.

`lower_match_case` now detects explicit enum/wildcard-only arms on the original
carrier and calls `lower_enum_match` before constructing `norm_arms`. Binding
and mixed-pattern cases retain the normalization path. The source contract is
pinned in `bootstrap_binary_lowering_source_spec.spl`; execution evidence still
requires rebuilding the affected compiler provider.

The repository's mandatory three-cycle bootstrap cap was reached in the GPU
dynamic-loading lane. Do not retry this full bootstrap in the same session.

## Vulkan Engine2D verification consequence

The canonical readback wrapper cannot use Stage 2 directly because that
bootstrap CLI deliberately has no `run` command. A direct Stage-2
`native-build` of the wrapper-generated evidence program was attempted once.
It discovered and parsed all **189/189** modules, including
`backend_vulkan.spl`, `backend_vulkan_spirv_raster_blobs.spl`,
`sffi_vulkan.spl`, and `sffi.dynamic.spl`, then failed while storing the first
lowered HIR module:

```text
[bootstrap-error-count] source_idx=0 point=post-lowering count=0
[bootstrap-error-count] source_idx=0 point=post-diagnostics count=0
error: hir codec: no `HirTypeKind` arm for tag -1;
       regenerate src/compiler/20.hir/generated/hir_codec.spl
```

No evidence executable was produced, so Vulkan availability, device identity,
present, readback, and pixel parity remain **not executed**, not failed. The
generated source and raw wrapper evidence are under
`build/vulkan-engine2d-readback-gpu-r3/` (ignored build artifacts).
