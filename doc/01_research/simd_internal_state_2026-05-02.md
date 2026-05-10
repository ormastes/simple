# Research: Internal SIMD State (2026-05-02)

**TL;DR:** The Simple compiler has a structurally complete but execution-shallow SIMD stack. The type layer has two competing representations (five hardcoded `struct Vec*` in `30.types/simd_vector_types.spl` that implement arithmetic element-wise in plain Simple, and a generic `SimdVectorType(element, lanes)` in `35.semantics/simd_check.spl`). The MIR has 19 concrete `SimdXxx` instruction variants covering add/sub/mul/div/fma/hadd/hmax/hmin for f32x4, f32x8, f64x4, i32x4, i32x8. `simd_lowering.spl` lowers `rt_simd_*` call-name strings to those MIR nodes; `auto_vectorize_codegen.spl` produces real `SimdAddF32x4` etc. from scalar loops. The x86_64 emitter (`x86_64_simd.spl`) and ARM NEON emitter (`arm_neon.spl`) emit concrete binary opcodes. **Critical gaps:** no SVE2 or RVV emitter, no AVX-512 emitter beyond the enum stub, no first-class Mask type anywhere in MIR, no gather/scatter MIR ops, no lane-cross permute/shuffle MIR ops, no scalable-vector lowering path, and the GPU path (though `cuda_backend.spl` and `vulkan_backend.spl` both exist) is limited to scalar PTX arithmetic + thread-ID intrinsics with no PTX vector types and no SPIR-V vector ops.

---

## 1. Type-System Surface Today

### 1a. `src/compiler/00.common/simd_types.spl` — 19 lines — STUB

File: `src/compiler/00.common/simd_types.spl:1-19`

Contains only two items:

```
enum SimdElementType { I8, I16, I32, I64, F32, F64 }
struct SimdVectorType { element: SimdElementType, lanes: i32 }
```

No constructors, no methods, no constants. The comment states it is "placed in 00.common to avoid backward dependency from 35.semantics -> 50.mir." It is the canonical shared contract, but it is a two-struct stub with zero logic.

### 1b. `src/compiler/30.types/simd_vector_types.spl` — 5 HARDCODED structs

File: `src/compiler/30.types/simd_vector_types.spl:12,57,323,395,440`

| Type | Kind | Lines |
|------|------|-------|
| `struct Vec2f` (x, y: f32) | concrete fixed | :12 |
| `struct Vec4f` (x, y, z, w: f32) | concrete fixed | :57 |
| `struct Vec8f` (x0–x7: f32) | concrete fixed | :323 |
| `struct Vec2d` (x, y: f64) | concrete fixed | :395 |
| `struct Vec4d` (x, y, z, w: f64) | concrete fixed | :440 |

All arithmetic methods (e.g., `Vec4f::add`, `Vec4f::mul`) are implemented as element-wise scalar Simple code — NOT as `rt_simd_*` intrinsic calls. No `Vec<N, T>` generic exists. No integer SIMD types (`Vec4i`, `Vec8i`) exist at the language-surface layer.

### 1c. `src/compiler/30.types/simd_platform.spl` — 387 lines — PARTIAL CONCRETE

`enum SimdPlatform` at line ~1: `None_Platform, SSE, SSE2, AVX, AVX2, AVX512, NEON, SVE`

`class SimdCapabilities` at line ~45: single-platform field (`platform: SimdPlatform`). Runtime detection reads `/proc/cpuinfo` for `avx512f`, `avx2`, `avx`, `sse2`, `sse`, `asimd`/`sve` flags (`detect_x86` / `detect_arm` fns). Falls back to architecture heuristics when `/proc/cpuinfo` absent.

`class SimdIntrinsics` exists as a placeholder: `sse_add_ps`, `sse_mul_ps`, etc. each delegate to `Vec4f::add` (scalar). These are documented as `# In real impl: __builtin_ia32_addps` but are not wired to `rt_simd_*`.

**Missing from `SimdCapabilities`:** no SVE2 bit, no VLEN field for SVE, no RVV/`has_riscv_v` field, no AVX-512 sub-feature flags (F/BW/DQ/VL), no NEON-FP16 bit.

### 1d. `src/compiler/35.semantics/simd_check.spl` — 544 lines — CONCRETE CHECK LAYER

`enum SimdElementType` (I8–F64, 6 variants) — mirrors `00.common` version but local.

`struct SimdVectorType { element_type: SimdElementType, lane_count: i64 }` with factory methods: `i8x16, i16x8, i32x4, i64x2, f32x4, f64x2`.

`enum SimdOperation`: Add/Sub/Mul/Div, And/Or/Xor/Not, Eq/Ne/Lt/Le/Gt/Ge, ReduceAdd/ReduceMul/ReduceMin/ReduceMax, Shuffle/Splat/Extract/Insert, Widen/Narrow/Convert. (~27 variants total, defined at :115.)

`enum SimdCheckError`: InvalidLaneCount, IncompatibleTypes, InvalidVectorWidth, UnsupportedOperation, LaneIndexOutOfBounds, ShuffleMaskInvalid. (Defined at :214.)

No `Mask` type exists in this layer.

### 1e. `src/compiler/50.mir/mir_types.spl` — MIR vector types

Fixed-width MIR types at :139–144: `Vec4f, Vec8f, Vec4d, Vec4i, Vec8i`. These match the MIR `SimdXxx` instruction operands exactly.

Scalable-vector placeholder at :170:
```
ScalableVec(element: MirType, min_lanes: i64)
# Scalable vector (LLVM <vscale x N x ty>) — lowering deferred until riscv_v ISel exists
```
**No lowering path exists for `ScalableVec`.**

### 1f. `src/compiler/70.backend/portable_numeric_capabilities.spl` — 186 lines

`struct PortableNumericCapabilities`: `has_scalar_fp, has_vector_simd, has_riscv_f, has_riscv_d, has_riscv_v, has_avx, has_avx2` plus `requires_runtime_simd_probe`.

`fn portable_numeric_capabilities_for_preset(preset)` maps `TargetPreset` fields (`arch`, `float_support`) to the capability struct. Exists as architecture-neutral registry per REQ-PSFM-001–011.

**Missing:** no `has_neon`, `has_sve`, `has_sve2`, `has_avx512` fields. `has_riscv_v` exists but no RVV emitter downstream.

*Cross-ref: `doc/04_architecture/portable_simd_fp_modules.md` — the PSFM architecture document defines REQ-PSFM-001–011 for this capability registry.*

---

## 2. Lowering Pipeline Today

**Claim:** the path for `Vec4f::add` does NOT go through SIMD MIR today.

Trace:

1. **Source:** `a.add(b)` on a `Vec4f` value.
2. **HIR:** `mir_lowering_expr.spl:17` imports `is_gpu_intrinsic` but contains NO SIMD intrinsic intercept for `Vec4f::add`. The call resolves as a normal method call.
3. **MIR:** The call is emitted as a regular `Call(dest, func_sym, args)` MIR node. No `SimdAddF32x4` is produced.
4. **simd_lowering.spl:93** (`run_simd_lowering`): the pass matches function names `rt_simd_add_f32x4`, `rt_simd_sub_f32x4`, etc. by string comparison on `Call.func`. `Vec4f::add` does NOT match — it is a method, not a `rt_simd_*` free function.

**Conclusion:** `Vec4f::add` currently executes as scalar element-wise arithmetic, never producing `SimdAddF32x4`. The SIMD MIR instructions are only reachable by:
- Calling `rt_simd_add_f32x4(a, b)` directly (free function intrinsic), **or**
- The auto-vectorizer (`auto_vectorize_codegen.spl:211`) upgrading a scalar BinOp loop.

The `simd_lowering.spl` pass name-matches at the `rt_simd_*` prefix (file:93–149 for both `try_lower_simd_call` and `try_lower_simd_intrinsic`). Recognition is **string-name matching only** — no structural type check, no HIR type annotation routing.

The MIR `SimdAddF32x4` → machine instruction path goes through `70.backend/backend/common/mir_text_codegen.spl:115` (`translate_simd_binop`) which emits a text opcode string. The **binary emitters** (`arm_neon.spl`, `x86_64_simd.spl`) contain the real encoding logic but wire is through `MachInst` construction, not through `mir_text_codegen`. The connection between `mir_text_codegen` SIMD dispatch and the binary emitters is not confirmed wired end-to-end from available code.

---

## 3. Strict-Emit Pattern (load-bearing template for SVE2/RVV)

### `arm_neon.spl` — 383 lines

`use compiler.backend.native.mach_inst.{MachReg, MachRegKind, physical_reg, reg_id, Operand, OperandKind, MachInst, ...}` (line :21).

Pattern:
1. `fn neon_encode_f32x4_3reg(opcode_bits, qd, qn, qm) -> [i64]` (line :71): encodes a 3-register A64 NEON encoding. Returns a list of i64 instruction words.
2. Named wrappers (e.g. `fn emit_fadd_f32x4(qd, qn, qm)` at :138): call `encode_neon_f32x4_3reg(0x4E20D400, ...)`. Hardcoded opcodes for FADD, FMUL, FSUB, FDIV, FMLA (f32x4), FADD/FMUL/FSUB/FDIV/FMLA (f64x2), ADD/SUB/MUL (i32x4). Covers all MIR `SimdXxx` ops that exist for f32x4, f64x2, i32x4.
3. Register IDs: `physical_reg(MachRegKind.Neon128, id)` pattern. `ymm_to_index` / `xmm_to_index` pattern on x86.

The existing pattern uses a 3-register encoding helper plus named opcode wrappers. `MachRegKind.Neon128` is the register class in use. No `MachRegKind.Sve` variant and no SVE-predicate operand model exist in the current source.

### `x86_64_simd.spl` — 411 lines

`fn _encode_simd_3op_ymm(dest, src1, src2, mmmmm, w, pp, opcode) -> [i64]` (line :152): builds 3-byte VEX prefix + ModRM. XMM range 16–31, YMM range 32–47 (by convention of register allocator IDs).

Wrappers: `encode_vaddps_ymm` (:167), `encode_vsubps_ymm` (:171), `encode_vmulps_ymm`, `encode_vdivps_ymm`, plus SSE 128-bit XMM variants via `_encode_simd_3op_xmm`. Integer AVX2 (VPADDD etc.) present.

No ZMM/EVEX emitter exists. `SimdPlatform.AVX512` is an enum variant but there is no `_encode_simd_3op_zmm`, no `zmm_to_index`, and no `MachRegKind.Zmm`. The existing VEX-prefix 3-op pattern covers up to YMM (256-bit) only.

---

## 4. Platform Detection / Capabilities

| Feature | Detected | How | Missing |
|---------|----------|-----|---------|
| SSE/SSE2/AVX/AVX2/AVX512 (x86) | yes | `/proc/cpuinfo` flag scan, `detect_x86` in `simd_platform.spl` | No sub-feature flags (BW/DQ/VL for AVX-512) |
| NEON (ARM) | yes | `/proc/cpuinfo` `asimd` or `neon` flag, `detect_arm` | No NEON-FP16 bit |
| SVE (ARM) | enum variant only | `/proc/cpuinfo` `sve` flag detected | No SVE2 distinction, no VLEN read (SVE `register_width()` returns 0) |
| SVE2 (ARM) | missing | — | Enum has `SVE` only; no `SVE2` variant; no `has_sve2()` fn |
| RVV (RISC-V V) | `has_riscv_v` in `PortableNumericCapabilities` | `TargetPreset` field mapping only | No runtime `vlenb` probe, no `has_riscv_zvfh` |
| AVX-512 sub-features | missing | — | `has_avx512()` bool exists but no F/BW/DQ/VL split |

`SimdCapabilities` in `simd_platform.spl` stores a single `platform: SimdPlatform` value — only the highest detected ISA level, not a bitmask. This means it cannot represent `has_avx2 AND has_avx512bw` simultaneously.

`PortableNumericCapabilities` in `portable_numeric_capabilities.spl` has individual booleans but misses NEON, SVE, SVE2 fields.

---

## 5. GPU / CUDA Path

### `src/compiler/70.backend/gpu_intrinsics.spl` — 243 lines

`fn recognize_gpu_intrinsic(name: text) -> GpuIntrinsicKind?` (line :17): name-string dispatch. Covers:
- Thread IDs: `gpu_global_id`, `gpu_local_id`, `gpu_block_id`, `gpu_block_dim`, `gpu_grid_dim` plus `_x`/`_y` suffixed variants.
- Sync: `gpu_sync`, `gpu_barrier`, `gpu_syncthreads`, `gpu_mem_fence`.
- Atomics: `gpu_atomic_add/sub/min/max/and/or/xor/exchange/cas`.

**Missing from `gpu_intrinsics.spl`:** no warp-level intrinsics (`shfl`, `vote`, `reduce`), no tensor core ops, no SIMD vector ops for GPU (PTX `.v4.f32` etc.).

### `src/compiler/70.backend/backend/cuda/ptx_builder.spl` — 538 lines

`class PtxBuilder` (line :14): emits PTX text. Covers:
- `emit_get_thread_id` (:138), `emit_get_block_id` (:147), `emit_get_grid_dim` (:165).
- Arithmetic: `emit_add/sub/mul/div` for scalar types via `ptx_type(ty)` string dispatch (:197–234).
- Intrinsics: `emit_intrinsic_sin/cos/sqrt/abs/min/max/fma/ex2/lg2/rcp` (:446–500).
- Barrier: `bar.sync 0` (:304).

**Missing:** no PTX vector types (`.v2`, `.v4`), no `shfl.sync`, `vote.sync`, `reduce`, no tensor core (`wmma.*`), no `ld.global.v4`, no `st.global.v4`.

### `src/compiler/70.backend/backend/cuda/cuda_launcher.spl` — 210 lines

Exists (not empty). Not audited in detail; named for kernel launch coordination.

### `src/compiler/70.backend/backend/cuda_backend.spl` — 760 lines

`class CudaBackend` at :18: fields `type_mapper: CudaTypeMapper`, `compute_capability: (i64, i64)`, `options: CompileOptions`. Implements both `Codegen` and `GpuCodegen` traits.

Key methods:
- `compile(module: MirModule) -> Result<CudaCompiledModule, CompileError>` (:71): iterates `module.functions`, calls `compile_function`, emits kernel headers via `PtxBuilder`, collects `CudaKernel` / `CudaDeviceFunction` structs.
- `compile_function(builder: PtxBuilder, func: MirFunction)` (:113): calls `builder.emit_kernel_entry` or `emit_device_function`, then iterates basic blocks emitting labels and instructions.
- `is_kernel_function(func: MirFunction)` (:156): checks `func.is_kernel` flag.
- `emit_local_decl(builder: PtxBuilder, local: MirLocal)` (:170): maps `MirType` to `PrimitiveType` for register declarations.
- `impl GpuCodegen`: `compile_kernel`, `compile_device_function`, `compile_barrier` (Workgroup → `bar.sync 0`, Device → `membar.gl`, Subgroup → `// warp sync`), `compile_atomic` (stub: `"// atomic op"`).

Note: the file lives at `70.backend/backend/cuda_backend.spl` (not inside a `cuda/` subdirectory).

**Gaps in `cuda_backend.spl`:** no SimdXxx MIR instruction handling (no vector register allocation, no PTX `.v4` instruction emission), `compile_gpu_instruction` returns `"// cuda instruction"` (stub), `compile_atomic` returns `"// atomic op"` (stub), `is_kernel_function` on `MirBody` always returns `false` (stub in the GpuCodegen impl).

### `src/compiler/70.backend/backend/vulkan/spirv_builder.spl` — 601 lines

`class SpirvBuilder` (line :14): emits SPIR-V assembly text. Covers:
- `emit_header`, `emit_memory_model` (GLSL450 + Logical), `emit_entry_point` (:122).
- Decorations: `DescriptorSet/Binding/BuiltIn/ArrayStride` (:139–153).
- Type emitters: `emit_type_vector` (:205), `OpLoad/OpStore` (:370–375).
- Arithmetic: `OpIMul` (:401), `OpFAdd` (:419). Limited coverage.
- Barriers: `emit_control_barrier/emit_memory_barrier` (:492–498).

**Missing:** no `OpFMul/OpFSub/OpFDiv` wired (OpFAdd only), no `OpGroupNonUniformBallot/ShuffleXor` (subgroup), no `OpCooperativeMatrix`, no `OpVectorShuffle`, no reduction group ops.

### `src/compiler/70.backend/backend/vulkan_backend.spl` — 479 lines

`class VulkanBackend` at :18: fields `type_mapper: VulkanTypeMapper`, `vulkan_version: [i64]`, `options: CompileOptions`.

Key methods:
- `compile(module: MirModule) -> text` (:71): calls `builder_emit_header/capabilities/extensions/memory_model`, then iterates functions, identifies compute shaders via `is_compute_shader`, calls `compile_compute_shader`, returns SPIR-V assembly text.
- `is_compute_shader(func: MirFunction) -> bool` (:104): scans basic block instructions for GPU instruction nodes.
- `compile_compute_shader(builder: SpirvBuilder, func: MirFunction)` (:116): emits void/bool/int/float types, `uvec3` type, `GlobalInvocationId`/`LocalInvocationId`/`WorkgroupId` builtins, entry point, workgroup size via `builder_emit_execution_mode`.

Note: the file lives at `70.backend/backend/vulkan_backend.spl` (not inside a `vulkan/` subdirectory).

**Gaps in `vulkan_backend.spl`:** `compile` returns `text` (not `Result<…>`), `for_target` returns `text` (both typed as stubs). No SimdXxx MIR → SPIR-V vector instruction path. `VulkanCompiledModule` and `VulkanComputeShader` result structs are defined at the tail of the file.

### `src/lib/nogc_sync_mut/cuda/` — 3 files (ffi.spl, mod.spl, __init__.spl)

`ffi.spl` declares `cuda_malloc, cuda_free, cuda_memcpy, cuda_launch_kernel, cuda_stream_create` as extern bindings to `src/compiler_rust/runtime/`. No SIMD vector ops at library level.

### `src/lib/nogc_sync_mut/gpu/` — 5 files (context, device, memory, mod, __init__)

High-level GPU context/device/memory wrappers. No SIMD vector or kernel dispatch ops exposed at user level.

### End-to-end CUDA / Vulkan kernel codegen verdict

**CUDA:** `cuda_backend.spl` (760 lines) and `ptx_builder.spl` (538 lines) exist and are connected — `CudaBackend.compile_function` calls `PtxBuilder` directly. The driver handles scalar MIR instructions and kernel/device-function entry/exit boilerplate. **Gap:** no SimdXxx → PTX vector instruction path; `compile_gpu_instruction` is a stub returning a comment string; vector types (`.v4.f32` etc.) are absent from `PtxBuilder`.

**Vulkan:** `vulkan_backend.spl` (479 lines) and `spirv_builder.spl` (601 lines) exist. `VulkanBackend.compile_compute_shader` emits type declarations and builtin variable decorations via `SpirvBuilder`. **Gap:** `compile` and `for_target` have stub return types (`text` not `Result<VulkanCompiledModule, CompileError>`); no SimdXxx → OpFMul/OpFSub/OpFDiv path; no SPIR-V vector op emission beyond what `spirv_builder.spl` already covers.

Kernel launch at runtime goes through `cuda_launcher.spl` and `lib/cuda/ffi.spl` (FFI bindings); this is orthogonal to the compiler-side codegen path.

*Cross-refs: `doc/04_architecture/gpu_acceleration_plan.md` (GPU acceleration architecture); `doc/04_architecture/compositor_gpu_architecture.md` (three-layer GPU/compositor model).*

---

## 6. Auto-Vectorization

Five files under `src/compiler/60.mir_opt/mir_opt/`:

| File | Lines | Role |
|------|-------|------|
| `auto_vectorize_types.spl` | 31 | Shared types: `LoopInfo`, `ArrayAccess` |
| `auto_vectorize_analysis.spl` | 483 | Dependency analysis |
| `auto_vectorize_validate.spl` | 245 | Vectorizability check: control flow, trip count, function calls, array access |
| `auto_vectorize_cost.spl` | 232 | Cost model: estimates scalar vs vector cost; profitable if speedup > 1.5× |
| `auto_vectorize_codegen.spl` | 316 | Emits real MIR `SimdXxx` instructions |

`auto_vectorize_codegen.spl:206` (`vectorize_binop`): produces **real** `MirInstKind.SimdAddF32x4`, `SimdAddF32x8`, `SimdAddF64x4`, `SimdAddI32x4`, `SimdAddI32x8` (and Sub/Mul/Div variants) based on a `VectorizeContext` that carries `vector_width` and `element_type`.

`vectorize_load/vectorize_store` (:264–309): emit `Intrinsic(load_name, [ptr])` / `Intrinsic(store_name, [ptr, value])` — using string-named intrinsics for vectorized memory access, not a dedicated `SimdLoad/SimdStore` MIR instruction.

**Auto-vectorizer does produce real SIMD MIR** for Add/Sub/Mul/Div. The cost model (`auto_vectorize_cost.spl`) is concrete (instruction-count based). `estimate_trip_count` is present. Whether the full pass is wired into the compilation pipeline (i.e., called from the MIR optimization driver) is not confirmed from available grep — no call site found in this audit.

*Cross-ref: `doc/01_research/domain/cpu_simd_scheduling.md` — TBB-style work-stealing scheduler design for `@simd` kernels; complements the vectorizer's cost model.*

---

## 7. Gap Map

| Capability | Status | File:line / Notes |
|------------|--------|-------------------|
| FixedVec concrete (Vec4f/Vec8f/etc.) | exists | `30.types/simd_vector_types.spl:57,323,440` — scalar impl only |
| FixedVec generic `Vec<N,T>` | missing | No generic vector type anywhere |
| FixedVec MIR types (Vec4f/Vec8f/Vec4d/Vec4i/Vec8i) | exists | `50.mir/mir_types.spl:139–144` |
| FixedVec MIR instructions (add/sub/mul/div/fma, hadd/hmax/hmin) | exists | `50.mir/mir_instructions.spl:88–116` |
| ScalableVec MIR type | partial | `50.mir/mir_types.spl:170` — stub, no lowering |
| ScalableVec lowering | missing | Deferred per comment |
| Mask type (first-class, in MIR or type system) | missing | Not in `mir_types.spl`, `simd_check.spl`, or `00.common/simd_types.spl` |
| SSE/SSE2/AVX/AVX2 emit | exists | `70.backend/backend/native/x86_64_simd.spl:152+` |
| AVX-512 emit | missing | `SimdPlatform.AVX512` enum exists; no ZMM/EVEX emitter |
| NEON-128 emit | exists | `70.backend/backend/native/arm_neon.spl:71+` |
| SVE2 emit | missing | No file, no `MachRegKind.Sve`, no predicate register model |
| RVV emit | missing | `has_riscv_v` in capabilities; no emitter file |
| Predication (mask-based conditional exec) | missing | No opmask reg model, no predicate operand in `MachInst` |
| Gather/scatter MIR ops | missing | Not in `mir_instructions.spl` |
| Reduction primitives MIR (beyond hadd/hmax/hmin f32x4) | partial | Only 3 horizontal ops in MIR; `SimdOperation` enum has ReduceAdd/Mul/Min/Max but not wired to MIR variants |
| Lane-cross permute/shuffle MIR ops | missing | Not in `mir_instructions.spl`; `SimdOperation.Shuffle` exists in semantics but has no MIR variant |
| SIMD intrinsic → MIR path (rt_simd_* string matching) | exists | `60.mir_opt/mir_opt/simd_lowering.spl:93–149` |
| Vec4f::add → SIMD MIR path | missing | `30.types/simd_vector_types.spl:116` is scalar; no HIR intercept |
| Auto-vectorizer producing SIMD MIR | exists | `60.mir_opt/mir_opt/auto_vectorize_codegen.spl:211` |
| Auto-vectorizer wired into pipeline | unknown | No call site confirmed in this audit |
| GPU intrinsic recognition (thread ID, sync, atomics) | exists | `70.backend/gpu_intrinsics.spl:17–47` |
| GPU warp dispatch (shfl/vote/reduce) | missing | Not in `gpu_intrinsics.spl` |
| PTX scalar arithmetic emit | exists | `70.backend/backend/cuda/ptx_builder.spl:197–234` |
| PTX vector types (.v4.f32 etc.) | missing | Not in `ptx_builder.spl` |
| PTX warp-level ops (shfl.sync, vote) | missing | Not in `ptx_builder.spl` |
| CUDA kernel codegen end-to-end (scalar) | partial | `cuda_backend.spl` (760L) exists; scalar MIR → PTX; SimdXxx handling absent; `compile_gpu_instruction` is stub |
| SPIR-V type/arith/load/store/barrier emit | partial | `70.backend/backend/vulkan/spirv_builder.spl`: OpFAdd, OpIMul, OpLoad, OpStore, barriers — limited op set |
| Vulkan compute shader codegen end-to-end (scalar) | partial | `vulkan_backend.spl` (479L) exists; compute shader skeleton; `compile`/`for_target` return stub `text`; no SimdXxx → SPIR-V vector path |
| SPIR-V subgroup/reduction ops | missing | Not in `spirv_builder.spl` |
| Platform detection mechanism (x86, ARM) | exists | `30.types/simd_platform.spl`: `/proc/cpuinfo` parse |
| Platform detection (RVV runtime) | missing | Only preset-time flag; no `vlenb` runtime probe |
| SVE VLEN detection | missing | `SVE register_width()` returns 0; no `vlenb`-equivalent |
| `PortableNumericCapabilities` registry | partial | `70.backend/portable_numeric_capabilities.spl`: has AVX/AVX2/RVV fields; missing NEON/SVE/SVE2/AVX-512 fields |
| GPU testing helpers | partial | `src/lib/nogc_sync_mut/src/testing/gpu_helpers.spl`: skip utilities only, no SIMD test infrastructure |
| CUDA FFI bindings (lib) | exists | `src/lib/nogc_sync_mut/cuda/ffi.spl` — malloc/free/memcpy/launch_kernel |
| CUDA SIMD vector ops (lib) | missing | No `.v4` or `[u8]`-packed vector op in `cuda/ffi.spl` |

**Row count: 35**

---

## 8. Anti-Pattern Flags

### Confirmed: `simd_vector_types.spl` arithmetic is scalar, not SIMD

`src/compiler/30.types/simd_vector_types.spl:116–145`:

```
fn add(other: Vec4f) -> Vec4f:
    Vec4f(x: self.x + other.x, y: self.y + other.y, z: self.z + other.z, w: self.w + other.w)
```

All five types (Vec2f, Vec4f, Vec8f, Vec2d, Vec4d) implement arithmetic as scalar field operations in plain Simple — not via `rt_simd_*` intrinsic calls, and therefore never producing `SimdAddF32x4` (or any other `SimdXxx`) MIR instruction. This is a structural disconnect: the hardcoded scalar structs and the generic `SimdVectorType(element, lanes)` in `simd_check.spl` are unconnected parallel representations with no shared lowering path.

### Confirmed: `SimdCapabilities` stores a single platform level, not a bitmask

`src/compiler/30.types/simd_platform.spl`: `class SimdCapabilities { platform: SimdPlatform }`. A single-value field cannot represent a CPU that has both AVX2 and AVX-512BW (they are modeled as separate enum variants, not independent bits). Any code that calls `has_avx2()` and then `has_avx512()` separately gets inconsistent results if the detected level is exactly AVX-512 (because `has_avx512()` returns `true` but `has_avx2()` may depend on the match arm ordering).

### Confirmed: `SimdIntrinsics` in `simd_platform.spl` is a dead layer

`class SimdIntrinsics` (at ~line 260 in `simd_platform.spl`): each method delegates to `Vec4f::add`, `Vec4f::mul`, etc. with comment `# In real impl: __builtin_ia32_addps`. This class adds no value over direct Vec4f calls. It is not referenced by any lowering pass. Candidate for removal.

### Confirmed: `cuda_backend.spl` and `vulkan_backend.spl` exist but are partially stubbed

Both files exist on disk at `70.backend/backend/cuda_backend.spl` (760 lines) and `70.backend/backend/vulkan_backend.spl` (479 lines). The backend driver layer is present, but critical methods are stubs: `compile_gpu_instruction` returns `"// cuda instruction"`, `compile_atomic` returns `"// atomic op"`, and `VulkanBackend.compile`/`for_target` return `text` rather than typed `Result<…>` values. No SimdXxx MIR instruction is handled by either driver.

### Confirmed: duplicate `SimdElementType` definitions

`src/compiler/00.common/simd_types.spl` and `src/compiler/35.semantics/simd_check.spl` both define `enum SimdElementType` independently with identical variants. The `simd_check.spl` version has additional methods (`to_text`, `bit_width`, `is_integer`, `is_float`). This duplication should be resolved by `simd_check.spl` importing from `00.common`.

---

## File Inventory Summary

| File | Lines | Classification |
|------|-------|----------------|
| `00.common/simd_types.spl` | 19 | stub |
| `30.types/simd_vector_types.spl` | ~500 est | concrete-fixed, scalar impl |
| `30.types/simd.spl` | 665 | test file (Phase 9A–9C tests) |
| `30.types/simd_platform.spl` | 387 | partial concrete (detection + dead intrinsic layer) |
| `35.semantics/simd_check.spl` | 544 | concrete check layer |
| `35.semantics/gpu_checker.spl` | 315 | concrete (kernel annotation validator) |
| `50.mir/mir_types.spl` | 291 | concrete fixed types + ScalableVec stub |
| `50.mir/mir_instructions.spl` | 545 | concrete (19 SimdXxx variants) |
| `50.mir/mir_lowering_expr.spl` | 1238 | partial (GPU intrinsics wired; SIMD not wired) |
| `60.mir_opt/mir_opt/simd_lowering.spl` | 203 | concrete (rt_simd_* name-match lowering) |
| `60.mir_opt/mir_opt/auto_vectorize_types.spl` | 31 | concrete |
| `60.mir_opt/mir_opt/auto_vectorize_analysis.spl` | 483 | concrete |
| `60.mir_opt/mir_opt/auto_vectorize_validate.spl` | 245 | concrete |
| `60.mir_opt/mir_opt/auto_vectorize_cost.spl` | 232 | concrete |
| `60.mir_opt/mir_opt/auto_vectorize_codegen.spl` | 316 | concrete (real SimdXxx MIR output) |
| `70.backend/portable_numeric_capabilities.spl` | 186 | partial (missing NEON/SVE/AVX-512 fields) |
| `70.backend/gpu_intrinsics.spl` | 243 | concrete (thread ID + atomics; no warp ops) |
| `70.backend/backend/native/arm_neon.spl` | 383 | concrete emitter |
| `70.backend/backend/native/x86_64_simd.spl` | 411 | concrete emitter (SSE/AVX/AVX2; no AVX-512) |
| `70.backend/backend/cuda/ptx_builder.spl` | 538 | partial (scalar only; no vectors/warp) |
| `70.backend/backend/cuda/cuda_launcher.spl` | 210 | exists (not fully audited) |
| `70.backend/backend/cuda_backend.spl` | 760 | partial (scalar MIR→PTX driver; SimdXxx stub; compile_gpu_instruction stub) |
| `70.backend/backend/vulkan/spirv_builder.spl` | 601 | partial (limited op set) |
| `70.backend/backend/vulkan_backend.spl` | 479 | partial (compute shader skeleton; compile/for_target return stub text) |
| `src/lib/nogc_sync_mut/cuda/ffi.spl` | exists | concrete FFI bindings |
| `src/lib/nogc_sync_mut/gpu/` | 5 files | concrete (device/memory/context, no vector ops) |
