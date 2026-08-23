# MIR Construct Coverage Matrix — 2026-08-23

**A known-coverage map for `src/compiler/50.mir/**` and the MIR->backend contract surface.** Derived from the CODE at `origin/main` (`267debf50f0`) and cross-checked against `spec/compiler_schema/registry/`. Gaps are named, not hidden.

Regenerate/verify: `sh scripts/check/check-mir-backend-coverage.shs`

## 0. What each column claims (read this first)

| term | meaning |
|---|---|
| **enumerated** | the variant exists in `src/compiler/50.mir/**`. |
| **lowered by N/10** | N of the 10 surveyed backend dispatch sites have a `case` arm for it. |
| **mentioned** | some `.spl` under `test/01_unit`/`test/unit` names it. **This is NOT verification** — a mention can be an incidental fixture constructor. |
| **verified** | a test asserts a VALUE produced by the construct, with the engine named. |

The interpreter and the native/JIT path resolve independently, so an assertion pinning one proves nothing about the other. Every 'verified' cell names its engine.

## 1. Enumeration totals

- **39 enums / 375 variants** in `src/compiler/50.mir/**` (full list: `mir_construct_census.json`).
- **126 `MirInstKind` instruction constructs** — the primary matrix (section 3).
- **225 core constructs** across the 12 instruction/type/operand families.
- Remaining 27 enums (~150 variants) are support/verification vocabularies (`Vhdl*`, `Gpu*Scope`, `Effect`, `VerificationEffectV1`, `MirLowerError`) — enumerated, out of matrix scope, listed in section 5.

| family | source | variants | mentioned by >=1 test |
|---|---|---|---|
| `MirInstKind` | `src/compiler/50.mir/mir_instruction_kinds.spl` | 126 | 82 |
| `MirTerminator` | `src/compiler/50.mir/mir_instruction_support.spl` | 7 | 7 |
| `MirTypeKind` | `src/compiler/50.mir/mir_types.spl` | 36 | 33 |
| `MirConstValue` | `src/compiler/50.mir/mir_types.spl` | 8 | 8 |
| `MirBinOp` | `src/compiler/50.mir/mir_instruction_support.spl` | 24 | 24 |
| `MirUnaryOp` | `src/compiler/50.mir/mir_instruction_support.spl` | 4 | 4 |
| `MirProjection` | `src/compiler/50.mir/mir_instruction_support.spl` | 4 | 2 |
| `MirOperandKind` | `src/compiler/50.mir/mir_instruction_support.spl` | 3 | 3 |
| `AggregateKind` | `src/compiler/50.mir/mir_instruction_support.spl` | 4 | 4 |
| `LocalKind` | `src/compiler/50.mir/mir_types.spl` | 4 | 4 |
| `MirBorrowKind` | `src/compiler/50.mir/mir_instruction_support.spl` | 2 | 2 |
| `MirTypeDefKind` | `src/compiler/50.mir/mir_types.spl` | 3 | 2 |

## 2. HIGHEST-VALUE FINDING — constructs reaching a silent fail-open catch-all

Each site below dispatches `match inst_kind:` and terminates in `case _:` that emits **nothing, with no diagnostic**. A construct outside its handled set is *deleted* from the generated code. That is a wrong answer, not an error — the exact defect class this lane exists for.

### 2.1 The five fail-open sites (no named error, silent drop)

| backend | source | `match` | `case _:` | handled | **silently dropped** |
|---|---|---|---|---|---|
| `cranelift_codegen_adapter` | `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl` | L503 | **L761** | 20/126 | **106** |
| `common/mir_text_codegen` | `src/compiler/70.backend/backend/common/mir_text_codegen.spl` | L57 | **L180** | 84/126 | **42** |
| `llvm_lib_translate_expr` | `src/compiler/70.backend/backend/llvm_lib_translate_expr.spl` | L69 | **L225** | 28/126 | **98** |
| `wasm/wat_codegen` | `src/compiler/70.backend/backend/wasm/wat_codegen.spl` | L230 | **L393** | 21/126 | **105** |
| `opencl_backend` | `src/compiler/70.backend/backend/opencl_backend.spl` | L153 | **L177** | 77/126 | **49** |

### 2.2 The five backends that already fail LOUD (lane C7, 2026-08-21)

These raise a named, spanned `E-BACKEND-*-INST-<Variant>` instead of dropping, and each has a transition table under `spec/compiler_schema/transitions/`. They are the model the five above should follow.

| backend | source | handled | unhandled | transition table |
|---|---|---|---|---|
| `C_backend` | `src/compiler/70.backend/backend/_CBackendTranslate/instruction_lowering.spl` | 126/126 | 0 | `mir_inst_to_c_backend.sdn` |
| `MirToLlvm_core` | `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` | 125/126 | 1 | `mir_inst_to_llvm.sdn` |
| `isel_x86_64` | `src/compiler/70.backend/backend/native/isel_x86_64.spl` | 126/126 | 0 | `mir_inst_to_native_isel.sdn` |
| `isel_aarch64` | `src/compiler/70.backend/backend/native/isel_aarch64.spl` | 16/126 | 110 | `mir_inst_to_native_isel.sdn` |
| `mir_interpreter` | `src/compiler/95.interp/mir_interpreter.spl` | 126/126 | 0 | `mir_inst_to_interp.sdn` |

> `isel_aarch64` shows 16/126 because it shares the `isel_x86_64` universe through a common dispatch; its own file handles only the arch-specific arms. Recorded as measured, not explained away.

### 2.3 Dropped by ALL FIVE fail-open backends — 25 constructs

No text/JIT backend lowers these at all. **This is the list the brief asked for.**

| construct | severity | consequence when dropped |
|---|---|---|
| `AcquireSnapshot` | CRITICAL | snapshot elided — reads observe live data instead of the snapshot. Silent wrong value. |
| `CommitUpdates` | CRITICAL | commit elided — the updates are silently discarded. Silent wrong value. |
| `Drop` | CRITICAL | WP-E affine `resource` drop edge. The release never happens — silent resource leak, and the exactly-once placement WP-E computes is discarded. |
| `FreezeRegion` | CRITICAL | region freeze elided — mutation of a frozen region is no longer prevented. |
| `HostGpuLaneBegin` | HIGH | host/GPU lane boundary erased — lane queue ordering unenforced. |
| `HostGpuLaneEnd` | HIGH | host/GPU lane boundary erased — lane queue ordering unenforced. |
| `MaskFromCmp` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `MaskedAdd` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `MaskedFma` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `MaskedMul` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `MirSimdPermute` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `MirSimdScalableVsetvl` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `MirSimdShuffle` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `MirWarpActivesMask` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `MirWarpBallot` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `MirWarpReduce` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `MirWarpShfl` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `MirWarpSync` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `PredicatedAdd` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `PredicatedFma` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `PredicatedMul` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `ResultMatchSemantic` | HIGH | result-match semantic marker dropped; error-propagation shape unpinned. |
| `ScalableVecFence` | HIGH | SIMD / warp / predicated-vector construct with **no scalar fallback emitted** — the operation vanishes from the output entirely. |
| `TransferIn` | CRITICAL | cross-domain ownership envelope erased; aliasing across execution domains goes unchecked. |
| `TransferOut` | CRITICAL | cross-domain ownership envelope erased; aliasing across execution domains goes unchecked. |

**Deliberately not fixed here.** A sibling lane owns the fail-open sites, and converting them to hard failures on the JIT path needs its own commit. Filed as `doc/08_tracking/bug/mir_constructs_silently_dropped_by_fail_open_backends_2026-08-23.md`.

### 2.4 Structural root cause

The five loud backends each have a transition table in `spec/compiler_schema/transitions/`; **the five fail-open backends have none.** The contract surface models 5 of 10 MIR consumers. There is no `mir_inst_to_cranelift`, `..._to_wasm`, `..._to_opencl`, `..._to_llvm_lib`, or `..._to_mir_text`. Nothing can ratchet a backend that is not modelled — which is precisely why these five stayed silent while the modelled five were repaired.

## 3. Per-construct matrix — `MirInstKind`

| # | construct | lowered by | dropped by fail-open | test mention | verified |
|---|---|---|---|---|---|
| 1 | `AcquireSnapshot` | 4/10 | 5/5 | `mir_transfer_operations_spec.spl` | **no** |
| 2 | `Aggregate` | 9/10 | 0/5 | `opencl_backend_contract_spec.spl` | **no** |
| 3 | `Alloc` | 10/10 | 0/5 | `opencl_backend_contract_spec.spl` | **no** |
| 4 | `Await` | 5/10 | 4/5 | `async_mir_spec.spl` | **no** |
| 5 | `BinOp` | 10/10 | 0/5 | `opencl_backend_contract_spec.spl` | **no** |
| 6 | `Bitcast` | 8/10 | 1/5 | `opencl_backend_contract_spec.spl` | **no** |
| 7 | `Call` | 9/10 | 1/5 | `resolve_nil_guard_spec.spl` | **no** |
| 8 | `CallIndirect` | 9/10 | 0/5 | `opencl_backend_contract_spec.spl` | **no** |
| 9 | `Cast` | 10/10 | 0/5 | `opencl_backend_contract_spec.spl` | **no** |
| 10 | `CheckedBinOp` | 9/10 | 0/5 | `opencl_backend_contract_spec.spl` | **no** |
| 11 | `CommitUpdates` | 4/10 | 5/5 | `mir_transfer_operations_spec.spl` | **no** |
| 12 | `Compose` | 6/10 | 3/5 | **none** | **no** |
| 13 | `ConditionProbe` | 7/10 | 3/5 | `wasm_mir_to_wat_spec.spl` | **no** |
| 14 | `Const` | 9/10 | 1/5 | `cuda_backend_intensive_contract_spec.spl` | **no** |
| 15 | `Copy` | 9/10 | 1/5 | `flat_ast_inline_asm_bridge_spec.spl` | **no** |
| 16 | `CreatePromise` | 5/10 | 4/5 | `async_mir_spec.spl` | **no** |
| 17 | `DebugValue` | 9/10 | 0/5 | `vhdl_backend_spec.spl` | **no** |
| 18 | `DecisionProbe` | 7/10 | 3/5 | `wasm_mir_to_wat_spec.spl` | **no** |
| 19 | `Drop` | 4/10 | 5/5 | `backend_silent_fallback_spec.spl` | **no** |
| 20 | `FreezeRegion` | 4/10 | 5/5 | **none** | **no** |
| 21 | `GetElementPtr` | 9/10 | 0/5 | `opencl_backend_contract_spec.spl` | **no** |
| 22 | `GetField` | 10/10 | 0/5 | `opencl_backend_contract_spec.spl` | **no** |
| 23 | `GpuAtomicCas` | 6/10 | 3/5 | `opencl_backend_contract_spec.spl` | **no** |
| 24 | `GpuAtomicOp` | 6/10 | 3/5 | `opencl_backend_contract_spec.spl` | **no** |
| 25 | `GpuBarrier` | 6/10 | 3/5 | `subgroup_intrinsics_contract_spec.spl` | **no** |
| 26 | `GpuBlockDim` | 6/10 | 3/5 | `cuda_backend_intensive_contract_spec.spl` | **no** |
| 27 | `GpuBlockId` | 6/10 | 3/5 | `cuda_backend_intensive_contract_spec.spl` | **no** |
| 28 | `GpuGlobalId` | 6/10 | 3/5 | `opencl_backend_contract_spec.spl` | **no** |
| 29 | `GpuGridDim` | 6/10 | 3/5 | `cuda_backend_intensive_contract_spec.spl` | **no** |
| 30 | `GpuKernelDef` | 5/10 | 4/5 | **none** | **no** |
| 31 | `GpuLaunch` | 5/10 | 4/5 | `mir_interp_silent_fallback_spec.spl` | **no** |
| 32 | `GpuLocalId` | 6/10 | 3/5 | `opencl_backend_contract_spec.spl` | **no** |
| 33 | `GpuMemFence` | 6/10 | 3/5 | `opencl_backend_contract_spec.spl` | **no** |
| 34 | `GpuSharedAlloc` | 6/10 | 3/5 | `opencl_backend_contract_spec.spl` | **no** |
| 35 | `HostGpuLaneBegin` | 4/10 | 5/5 | `host_gpu_lane_codegen_marker_spec.spl` | **no** |
| 36 | `HostGpuLaneEnd` | 4/10 | 5/5 | `host_gpu_lane_codegen_marker_spec.spl` | **no** |
| 37 | `InlineAsm` | 6/10 | 3/5 | **none** | **no** |
| 38 | `Intrinsic` | 10/10 | 0/5 | `subgroup_intrinsics_contract_spec.spl` | **no** |
| 39 | `LayerConnect` | 6/10 | 3/5 | **none** | **no** |
| 40 | `Load` | 10/10 | 0/5 | `opencl_backend_contract_spec.spl` | **no** |
| 41 | `LoadGlobal` | 5/10 | 4/5 | `vhdl_hardware_call_lowering_contract_spec.spl` | **no** |
| 42 | `MaskFromCmp` | 4/10 | 5/5 | `predicate_promote_spec.spl` | **no** |
| 43 | `MaskedAdd` | 4/10 | 5/5 | `predicate_promote_spec.spl` | **no** |
| 44 | `MaskedFma` | 4/10 | 5/5 | `predicate_promote_spec.spl` | **no** |
| 45 | `MaskedMul` | 4/10 | 5/5 | `predicate_promote_spec.spl` | **no** |
| 46 | `MirSimdBinop` | 5/10 | 4/5 | `opencl_backend_contract_spec.spl` | **no** |
| 47 | `MirSimdCmp` | 5/10 | 4/5 | `opencl_backend_contract_spec.spl` | **no** |
| 48 | `MirSimdGather` | 5/10 | 4/5 | `opencl_backend_contract_spec.spl` | **no** |
| 49 | `MirSimdLoad` | 5/10 | 4/5 | `opencl_backend_contract_spec.spl` | **no** |
| 50 | `MirSimdMaskOp` | 5/10 | 4/5 | `opencl_backend_contract_spec.spl` | **no** |
| 51 | `MirSimdPermute` | 4/10 | 5/5 | **none** | **no** |
| 52 | `MirSimdReduce` | 5/10 | 4/5 | `opencl_backend_contract_spec.spl` | **no** |
| 53 | `MirSimdScalableVsetvl` | 4/10 | 5/5 | **none** | **no** |
| 54 | `MirSimdScatter` | 5/10 | 4/5 | `opencl_backend_contract_spec.spl` | **no** |
| 55 | `MirSimdSelect` | 5/10 | 4/5 | `opencl_backend_contract_spec.spl` | **no** |
| 56 | `MirSimdShuffle` | 4/10 | 5/5 | **none** | **no** |
| 57 | `MirSimdSplat` | 5/10 | 4/5 | `opencl_backend_contract_spec.spl` | **no** |
| 58 | `MirSimdStore` | 5/10 | 4/5 | `opencl_backend_contract_spec.spl` | **no** |
| 59 | `MirSimdTernop` | 5/10 | 4/5 | `opencl_backend_contract_spec.spl` | **no** |
| 60 | `MirSimdUnop` | 5/10 | 4/5 | `opencl_backend_contract_spec.spl` | **no** |
| 61 | `MirWarpActivesMask` | 4/10 | 5/5 | **none** | **no** |
| 62 | `MirWarpBallot` | 4/10 | 5/5 | `backend_silent_fallback_spec.spl` | **no** |
| 63 | `MirWarpReduce` | 4/10 | 5/5 | **none** | **no** |
| 64 | `MirWarpShfl` | 4/10 | 5/5 | **none** | **no** |
| 65 | `MirWarpSync` | 4/10 | 5/5 | **none** | **no** |
| 66 | `Move` | 10/10 | 0/5 | `cuda_backend_intensive_contract_spec.spl` | **no** |
| 67 | `Nop` | 10/10 | 0/5 | `host_gpu_lane_codegen_marker_spec.spl` | **no** |
| 68 | `Parallel` | 6/10 | 3/5 | **none** | **no** |
| 69 | `PipeForward` | 6/10 | 3/5 | **none** | **no** |
| 70 | `PredicatedAdd` | 4/10 | 5/5 | `predicate_promote_spec.spl` | **no** |
| 71 | `PredicatedFma` | 4/10 | 5/5 | `predicate_promote_spec.spl` | **no** |
| 72 | `PredicatedMul` | 4/10 | 5/5 | `predicate_promote_spec.spl` | **no** |
| 73 | `Receive` | 5/10 | 4/5 | `async_mir_spec.spl` | **no** |
| 74 | `Ref` | 7/10 | 2/5 | `flat_ast_address_of_spec.spl` | **no** |
| 75 | `ResultMatchSemantic` | 4/10 | 5/5 | `mir_interp_silent_fallback_spec.spl` | **no** |
| 76 | `ScalableVecFence` | 4/10 | 5/5 | **none** | **no** |
| 77 | `Send` | 5/10 | 4/5 | `async_mir_spec.spl` | **no** |
| 78 | `SetField` | 10/10 | 0/5 | `opencl_backend_contract_spec.spl` | **no** |
| 79 | `SimdAddF32x4` | 6/10 | 3/5 | `opencl_backend_contract_spec.spl` | **no** |
| 80 | `SimdAddF32x8` | 6/10 | 3/5 | **none** | **no** |
| 81 | `SimdAddF64x4` | 6/10 | 3/5 | **none** | **no** |
| 82 | `SimdAddI32x4` | 6/10 | 3/5 | **none** | **no** |
| 83 | `SimdAddI32x8` | 6/10 | 3/5 | **none** | **no** |
| 84 | `SimdAndI32x4` | 6/10 | 3/5 | `opencl_backend_contract_spec.spl` | **no** |
| 85 | `SimdAndI32x8` | 6/10 | 3/5 | **none** | **no** |
| 86 | `SimdDivF32x4` | 6/10 | 3/5 | **none** | **no** |
| 87 | `SimdDivF32x8` | 6/10 | 3/5 | **none** | **no** |
| 88 | `SimdDivF64x4` | 6/10 | 3/5 | **none** | **no** |
| 89 | `SimdFmaF32x4` | 6/10 | 3/5 | `opencl_backend_contract_spec.spl` | **no** |
| 90 | `SimdFmaF32x8` | 6/10 | 3/5 | **none** | **no** |
| 91 | `SimdFmaF64x4` | 6/10 | 3/5 | **none** | **no** |
| 92 | `SimdHaddF32x4` | 6/10 | 3/5 | `opencl_backend_contract_spec.spl` | **no** |
| 93 | `SimdHmaxF32x4` | 6/10 | 3/5 | `opencl_backend_contract_spec.spl` | **no** |
| 94 | `SimdHminF32x4` | 6/10 | 3/5 | `opencl_backend_contract_spec.spl` | **no** |
| 95 | `SimdMulF32x4` | 6/10 | 3/5 | **none** | **no** |
| 96 | `SimdMulF32x8` | 6/10 | 3/5 | **none** | **no** |
| 97 | `SimdMulF64x4` | 6/10 | 3/5 | **none** | **no** |
| 98 | `SimdMulI32x4` | 6/10 | 3/5 | **none** | **no** |
| 99 | `SimdMulI32x8` | 6/10 | 3/5 | **none** | **no** |
| 100 | `SimdOrI32x4` | 6/10 | 3/5 | **none** | **no** |
| 101 | `SimdOrI32x8` | 6/10 | 3/5 | **none** | **no** |
| 102 | `SimdShlI32x4` | 6/10 | 3/5 | **none** | **no** |
| 103 | `SimdShlI32x8` | 6/10 | 3/5 | **none** | **no** |
| 104 | `SimdShrI32x4` | 6/10 | 3/5 | **none** | **no** |
| 105 | `SimdShrI32x8` | 6/10 | 3/5 | **none** | **no** |
| 106 | `SimdSubF32x4` | 6/10 | 3/5 | **none** | **no** |
| 107 | `SimdSubF32x8` | 6/10 | 3/5 | **none** | **no** |
| 108 | `SimdSubF64x4` | 6/10 | 3/5 | **none** | **no** |
| 109 | `SimdSubI32x4` | 6/10 | 3/5 | **none** | **no** |
| 110 | `SimdSubI32x8` | 6/10 | 3/5 | **none** | **no** |
| 111 | `SimdXorI32x4` | 6/10 | 3/5 | `opencl_backend_contract_spec.spl` | **no** |
| 112 | `SimdXorI32x8` | 6/10 | 3/5 | **none** | **no** |
| 113 | `Spawn` | 5/10 | 4/5 | `async_mir_spec.spl` | **no** |
| 114 | `Store` | 10/10 | 0/5 | `opencl_backend_contract_spec.spl` | **no** |
| 115 | `StoreGlobal` | 4/10 | 4/5 | `vhdl_hardware_call_lowering_contract_spec.spl` | **no** |
| 116 | `TransferIn` | 4/10 | 5/5 | `mir_transfer_operations_spec.spl` | **no** |
| 117 | `TransferOut` | 4/10 | 5/5 | `mir_transfer_operations_spec.spl` | **no** |
| 118 | `UnaryOp` | 10/10 | 0/5 | `flat_ast_address_of_spec.spl` | **no** |
| 119 | `VhdlConcat` | 5/10 | 4/5 | `vhdl_backend_spec.spl` | **no** |
| 120 | `VhdlPortMap` | 5/10 | 4/5 | `vhdl_design_catalog_spec.spl` | **no** |
| 121 | `VhdlProcess` | 5/10 | 4/5 | `target_family_package_surface_spec.spl` | **no** |
| 122 | `VhdlResize` | 5/10 | 4/5 | `vhdl_backend_spec.spl` | **no** |
| 123 | `VhdlSignalAssign` | 5/10 | 4/5 | **none** | **no** |
| 124 | `VhdlSlice` | 5/10 | 4/5 | `vhdl_backend_spec.spl` | **no** |
| 125 | `VhdlVarAssign` | 5/10 | 4/5 | **none** | **no** |
| 126 | `Yield` | 5/10 | 4/5 | `async_mir_spec.spl` | **no** |

> The `verified` column is honestly **no** for every row: no existing spec asserts a VALUE produced by a named `MirInstKind` through a stated engine. Section 7 records what this lane adds.

## 4. Other core families


### `MirTerminator` — 7/7 mentioned

| construct | test mention |
|---|---|
| `Goto` | `opencl_backend_contract_spec.spl` |
| `Ret` | `storage_simd_opencl_spec.spl` |
| `If` | `opencl_backend_contract_spec.spl` |
| `Switch` | `opencl_backend_contract_spec.spl` |
| `Unreachable` | `opencl_backend_contract_spec.spl` |
| `Abort` | `vhdl_backend_spec.spl` |
| `CallTerminator` | `vulkan_backend_intensive_spec.spl` |

### `MirTypeKind` — 33/36 mentioned

| construct | test mention |
|---|---|
| `I8` | `cuda_ptx_mir_kind_primitive_class_spec.spl` |
| `I16` | `cuda_ptx_mir_kind_primitive_class_spec.spl` |
| `I32` | `wasm_codegen_spec.spl` |
| `I64` | `wasm_codegen_spec.spl` |
| `U8` | `resolve_nil_guard_spec.spl` |
| `U16` | `cuda_ptx_mir_kind_primitive_class_spec.spl` |
| `U32` | `cuda_ptx_device_function_param_type_spec.spl` |
| `U64` | `resolve_nil_guard_spec.spl` |
| `F32` | `cuda_ptx_device_function_param_type_spec.spl` |
| `F64` | `wasm_codegen_spec.spl` |
| `Bool` | `wasm_codegen_spec.spl` |
| `Char` | `driver_manifest_test.spl` |
| `Unit` | `header_gen_spec.spl` |
| `Vec4f` | `opencl_backend_contract_spec.spl` |
| `Vec8f` | `storage_simd_opencl_spec.spl` |
| `Vec4d` | `opencl_backend_contract_spec.spl` |
| `Vec4i` | `opencl_backend_contract_spec.spl` |
| `Vec8i` | `opencl_backend_contract_spec.spl` |
| `Ptr` | `resolve_nil_guard_spec.spl` |
| `Ref` | `cuda_ptx_device_function_param_type_spec.spl` |
| `FuncPtr` | `resolve_nil_guard_spec.spl` |
| `Array` | `opencl_backend_contract_spec.spl` |
| `Dict` | `seed_parity_scalar_type_names_spec.spl` |
| `Slice` | `slice_spec.spl` |
| `Tuple` | `resolve_nil_guard_spec.spl` |
| `Struct` | `cuda_backend_intensive_contract_spec.spl` |
| `Enum` | `vhdl_backend_spec.spl` |
| `Result` | `backend_silent_fallback_spec.spl` |
| `Bits` | `backend_silent_fallback_spec.spl` |
| `Union` | **NONE** |
| `Never` | **NONE** |
| `Opaque` | `header_gen_spec.spl` |
| `ScalableVec` | `scalable_vec_mir_scaffolding_spec.spl` |
| `Promise` | `async_mir_spec.spl` |
| `Generator` | `async_mir_spec.spl` |
| `ActorType` | **NONE** |

### `MirConstValue` — 8/8 mentioned

| construct | test mention |
|---|---|
| `Int` | `narrowing_spec.spl` |
| `Float` | `enum_f64_payload_precision_spec.spl` |
| `Bool` | `narrowing_spec.spl` |
| `Str` | `resolve_nil_guard_spec.spl` |
| `Array` | `wasm_mir_to_wat_spec.spl` |
| `Tuple` | `isel_riscv32_spec.spl` |
| `Struct` | `cranelift_aggregate_runtime_abi_spec.spl` |
| `Zero` | `vhdl_backend_spec.spl` |

### `MirBinOp` — 24/24 mentioned

| construct | test mention |
|---|---|
| `Add` | `opencl_backend_contract_spec.spl` |
| `Sub` | `strength_reduction_spec.spl` |
| `Mul` | `opencl_backend_contract_spec.spl` |
| `Div` | `vulkan_backend_intensive_spec.spl` |
| `Rem` | `cuda_backend_intensive_contract_spec.spl` |
| `Pow` | `wasm_mir_to_wat_spec.spl` |
| `MatMul` | `backend_capability_spec.spl` |
| `BitAnd` | `strength_reduction_spec.spl` |
| `BitOr` | `strength_reduction_spec.spl` |
| `BitXor` | `strength_reduction_spec.spl` |
| `Shl` | `strength_reduction_spec.spl` |
| `Shr` | `strength_reduction_spec.spl` |
| `Eq` | `cuda_backend_intensive_contract_spec.spl` |
| `Ne` | `cuda_backend_intensive_contract_spec.spl` |
| `Lt` | `cuda_backend_intensive_contract_spec.spl` |
| `Le` | `wasm_mir_to_wat_spec.spl` |
| `Gt` | `wasm_mir_to_wat_spec.spl` |
| `Ge` | `cuda_backend_intensive_contract_spec.spl` |
| `BroadcastAdd` | `cranelift_gemm_fusion_spec.spl` |
| `BroadcastSub` | `cranelift_gemm_fusion_spec.spl` |
| `BroadcastMul` | `wasm_mir_to_wat_spec.spl` |
| `BroadcastDiv` | `wasm_mir_to_wat_spec.spl` |
| `BroadcastPow` | `wasm_mir_to_wat_spec.spl` |
| `Offset` | `wasm_mir_to_wat_spec.spl` |

### `MirUnaryOp` — 4/4 mentioned

| construct | test mention |
|---|---|
| `Neg` | `flat_ast_address_of_spec.spl` |
| `Not` | `cuda_backend_intensive_contract_spec.spl` |
| `BitNot` | `cuda_backend_intensive_contract_spec.spl` |
| `Transpose` | `backend_capability_spec.spl` |

### `MirProjection` — 2/4 mentioned

| construct | test mention |
|---|---|
| `Deref` | **NONE** |
| `Field` | `hir_stmt_dispatch_source_spec.spl` |
| `Index` | `hir_block_tail_invariants_source_spec.spl` |
| `Downcast` | **NONE** |

### `MirOperandKind` — 3/3 mentioned

| construct | test mention |
|---|---|
| `Copy` | `flat_ast_inline_asm_bridge_spec.spl` |
| `Move` | `var_reassign_analysis_spec.spl` |
| `Const` | `resolve_nil_guard_spec.spl` |

### `AggregateKind` — 4/4 mentioned

| construct | test mention |
|---|---|
| `Array` | `opencl_backend_contract_spec.spl` |
| `Tuple` | `vhdl_backend_spec.spl` |
| `Struct` | `vhdl_hardware_call_lowering_contract_spec.spl` |
| `Enum` | `vhdl_backend_spec.spl` |

### `LocalKind` — 4/4 mentioned

| construct | test mention |
|---|---|
| `Arg` | `storage_simd_opencl_spec.spl` |
| `Var` | `scalable_vec_mir_scaffolding_spec.spl` |
| `Temp` | `storage_simd_opencl_spec.spl` |
| `Return` | `vhdl_hardware_call_lowering_contract_spec.spl` |

### `MirBorrowKind` — 2/2 mentioned

| construct | test mention |
|---|---|
| `Shared` | `flat_ast_address_of_spec.spl` |
| `Mutable` | `flat_ast_address_of_spec.spl` |

### `MirTypeDefKind` — 2/3 mentioned

| construct | test mention |
|---|---|
| `Struct` | `header_gen_spec.spl` |
| `Enum` | `vhdl_backend_spec.spl` |
| `Union` | **NONE** |

## 5. Support / verification enums (enumerated, out of matrix scope)

| enum | source | variants |
|---|---|---|
| `AsyncEffect` | `src/compiler/50.mir/mir_effects.spl` | 3 |
| `BlockState` | `src/compiler/50.mir/mir_contract.spl` | 2 |
| `BuiltinFunc` | `src/compiler/50.mir/mir_effects.spl` | 28 |
| `Effect` | `src/compiler/50.mir/mir_effects.spl` | 7 |
| `ExecutionContractObligationKindV1` | `src/compiler/50.mir/verification_contract.spl` | 7 |
| `GpuAtomicOpKind` | `src/compiler/50.mir/mir_instruction_support.spl` | 9 |
| `GpuBarrierScope` | `src/compiler/50.mir/mir_instruction_support.spl` | 3 |
| `GpuMemoryScope` | `src/compiler/50.mir/mir_instruction_support.spl` | 4 |
| `LayoutPhase` | `src/compiler/50.mir/mir_types.spl` | 4 |
| `LowererState` | `src/compiler/50.mir/mir_contract.spl` | 2 |
| `MirExecutionDomain` | `src/compiler/50.mir/mir_instruction_support.spl` | 6 |
| `MirLowerError` | `src/compiler/50.mir/mir_contract.spl` | 6 |
| `MirRegionAccessV1` | `src/compiler/50.mir/verification_region_effects.spl` | 2 |
| `MirTransferMode` | `src/compiler/50.mir/mir_instruction_support.spl` | 5 |
| `MirTransferPayload` | `src/compiler/50.mir/mir_instruction_support.spl` | 7 |
| `NogcInstr` | `src/compiler/50.mir/mir_effects.spl` | 3 |
| `SemanticClass` | `src/compiler/50.mir/verification_ir.spl` | 4 |
| `SyntheticDriverRegistrationStatus` | `src/compiler/50.mir/synthetic_driver_registration.spl` | 5 |
| `VerificationContractClauseKindV1` | `src/compiler/50.mir/verification_contract.spl` | 6 |
| `VerificationContractOutcomeV1` | `src/compiler/50.mir/verification_contract.spl` | 2 |
| `VerificationEffectV1` | `src/compiler/50.mir/verification_effects.spl` | 14 |
| `VhdlClockEdge` | `src/compiler/50.mir/mir_instruction_support.spl` | 2 |
| `VhdlNumericKind` | `src/compiler/50.mir/mir_instruction_support.spl` | 5 |
| `VhdlPortDirection` | `src/compiler/50.mir/mir_instruction_support.spl` | 4 |
| `VhdlProcessKind` | `src/compiler/50.mir/mir_instruction_support.spl` | 3 |
| `VhdlSignalKind` | `src/compiler/50.mir/mir_instruction_support.spl` | 5 |
| `VhdlSignalResolution` | `src/compiler/50.mir/mir_instruction_support.spl` | 2 |

## 6. Code vs registry cross-check (a disagreement is itself a finding)

| family | code | registry | disagreement |
|---|---|---|---|
| `MirInstKind` | 126 | 126 | none |
| `MirTerminator` | 7 | 7 | none |
| `MirTypeKind` | 36 | 29 | **`F64`, `I16`, `I32`, `I64`, `U16`, `U32`, `U64`` missing from registry** |

### 6.1 CONFIRMED SOURCE BUG — the registry generator drops comma-listed variants

`compiler.mir.MirTypeKind.sdn` records **29** variants; the code declares **36**. The 7 missing are exactly `I16, I32, I64, U16, U32, U64, F64` — and in `mir_types.spl` those are exactly the variants that appear as the 2nd..4th token of a comma-separated line:

```
    I8, I16, I32, I64
    U8, U16, U32, U64
    F32, F64
```

`I8`, `U8` and `F32` (the FIRST token of each line) are present in the registry; every non-first token is absent. The generator reads one variant per line. Every downstream artifact keyed off this registry — including the `mir_type_to_c_backend` transition table — therefore has a 7-variant blind spot, and a backend that silently drops `I32` would be invisible to the schema gate. Filed as `doc/08_tracking/bug/compiler_schema_generator_drops_comma_listed_enum_variants_2026-08-23.md`. **Left RED — not repaired here** (`src/app/compiler_schema/**` is outside this lane's scope).

## 7. What this lane adds, and what remains unverified

- **Enumerated:** 39 enums / 375 variants; 126 instruction constructs; 225 core constructs.
- **Added gate:** `scripts/check/check-mir-backend-coverage.shs` — re-derives every backend's handled set from source and ratchets it against `mir_backend_coverage_baseline.txt`. Deleting a `case` arm, or adding a `MirInstKind` variant that no backend lowers, FAILs it.
- **Added spec:** `test/01_unit/compiler/mir/mir_construct_matrix_spec.spl` (mirrored in `test/unit/...`) — VALUE assertions over the construct families, engine named per assertion.
- **Still unverified (named):** all 126 `MirInstKind` constructs lack a value assertion tied to a named engine except those covered by the new spec; the 25 constructs in section 2.3 cannot be verified on any text/JIT backend at all, because no backend emits them.

### 7.1 Constructs with NO test mention anywhere


**MirInstKind** (44): `FreezeRegion`, `SimdSubF32x4`, `SimdMulF32x4`, `SimdDivF32x4`, `SimdAddF32x8`, `SimdSubF32x8`, `SimdMulF32x8`, `SimdDivF32x8`, `SimdFmaF32x8`, `SimdAddF64x4`, `SimdSubF64x4`, `SimdMulF64x4`, `SimdDivF64x4`, `SimdFmaF64x4`, `SimdAddI32x4`, `SimdSubI32x4`, `SimdMulI32x4`, `SimdOrI32x4`, `SimdShlI32x4`, `SimdShrI32x4`, `SimdAddI32x8`, `SimdSubI32x8`, `SimdMulI32x8`, `SimdXorI32x8`, `SimdAndI32x8`, `SimdOrI32x8`, `SimdShlI32x8`, `SimdShrI32x8`, `PipeForward`, `Compose`, `Parallel`, `LayerConnect`, `GpuKernelDef`, `VhdlSignalAssign`, `VhdlVarAssign`, `ScalableVecFence`, `MirSimdShuffle`, `MirSimdPermute`, `MirSimdScalableVsetvl`, `MirWarpShfl`, `MirWarpReduce`, `MirWarpActivesMask`, `MirWarpSync`, `InlineAsm`

**MirTypeKind** (3): `Union`, `Never`, `ActorType`

**MirProjection** (2): `Deref`, `Downcast`

**MirTypeDefKind** (1): `Union`

## 8. Measured results (2026-08-23)

### 8.1 Gate

```
$ sh scripts/check/check-mir-backend-coverage.shs --selftest
PASS — 5 selftest fixture(s) checked, 0 regressions

$ sh scripts/check/check-mir-backend-coverage.shs          # 0.8 s
PASS — 749 (backend,construct) pair(s) checked across 10 backend(s), 0 regressions, 0 orphans
```

**Neuter evidence against REAL source (not fixtures).** Both were restored and
re-verified PASS/exit 0 afterwards; `git status --porcelain src/` came back clean.

```
# neuter 1 — remove a real case arm from the interpreter
$ sed -i '289s/case BinOp(/case NEUTERED_BinOp(/' src/compiler/95.interp/mir_interpreter.spl
$ sh scripts/check/check-mir-backend-coverage.shs
regressed (case arm removed): mir_interpreter	BinOp
FAIL — 748 (backend,construct) pair(s) checked, 1 regression(s), 0 orphan construct(s)   # exit 1

# neuter 2 — add a MirInstKind variant that no backend lowers
$ # (added FabricatedConstruct to mir_instruction_kinds.spl)
$ sh scripts/check/check-mir-backend-coverage.shs
lowered by NO backend: FabricatedConstruct
FAIL — 749 (backend,construct) pair(s) checked, 0 regression(s), 1 orphan construct(s)   # exit 1
```

The gate's own `--selftest` additionally carries a dedicated neuter fixture
(f2: renaming `case Beta` must drop the derived set to `Alpha` only), so the
discrimination property is re-proved on every invocation rather than trusted.

### 8.2 Spec — `mir_construct_matrix_spec.spl`

Engine: **spec host / tree-walk** (`simple test`). Stated explicitly because the
native path resolves independently.

```
19 examples, 3 failures
16 passed, 3 failed
```

The 3 failures are exactly the RED block of section 2's sibling defect —
`expected 8 to equal 16`, `expected 8 to equal 32`, `expected 8 to equal 32` —
i.e. `MirType.size_bytes()` / `alignment()` returning the residual 8 for the SIMD
vector types. **Left RED deliberately**; filed as
`doc/08_tracking/bug/mir_type_simd_vector_size_bytes_returns_8_2026-08-23.md`.
The 16 green examples use the same helpers and the same matcher, so the RED trio
is direct evidence that these assertions discriminate on VALUE rather than on
absence-of-crash.

### 8.3 Spec neuter attempt — BLOCKED, stated rather than claimed

A source-level neuter of a GREEN assertion was attempted: `primitive_size()`'s
`case I8 | U8 | Bool: Some(1)` was changed to `Some(99)`, which must flip the
"gives each integer width its exact size in bytes" example to FAIL. The run was
**starved by host load** (load average 51, ~20 concurrent `simple` processes from
other lanes) and was killed by its own 1500 s timeout while still in session
setup, producing no verdict. The source was restored and verified clean
(`git status --porcelain src/` empty, 0 occurrences of the neuter token).

This is recorded as **not proved**, not as proved. What IS proved for the spec is
weaker but real: the 3 RED examples fail with `expected 8 to equal 16/32` through
the same `ty(...).size_bytes()` helper and the same matcher as the 16 green ones,
so the assertions demonstrably discriminate on VALUE. Re-run the neuter on an
idle host to close this gap:

```sh
sed -i 's/case I8 | U8 | Bool: Some(1)/case I8 | U8 | Bool: Some(99)/' src/compiler/50.mir/mir_types.spl
bin/simple test test/01_unit/compiler/mir/mir_construct_matrix_spec.spl   # expect 4 failures, not 3
git checkout -- src/compiler/50.mir/mir_types.spl
```

The GATE's neuter evidence (section 8.1) is unaffected — it runs in 0.8 s and was
proved twice against real source.
