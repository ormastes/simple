# Simple Optimization Architecture Roadmap

Lifecycle Profiling, HotSpot Optimization, Binary Optimization, and Algorithm Provider Framework

- **Status:** Proposal
- **Target:** https://github.com/ormastes/simple
- **Version:** 2.0
- **Date:** 2026-06-01

---

## 1. Goals

Simple should support optimization throughout the entire software lifecycle:

```
Source → Parser → HIR → MIR → SMF → Interpreter → JIT → Native → Runtime → Production Feedback → Next Build
```

Unlike traditional compilers that optimize only during compilation, Simple should continuously optimize using runtime feedback, persistent profiles, and version-aware migration.

### Primary Goals

1. Java HotSpot-like runtime optimization with tiered compilation.
2. Persistent SMF profile collection (`.sprof`).
3. Cross-version profile migration using MIR hash matching.
4. LLVM PGO + BOLT binary optimization.
5. Automatic CPU/SIMD/GPU/offload algorithm selection via provider framework.
6. Optimization traceability — fact-driven proof at every tier.
7. Safe deoptimization with interpreter fallback.
8. Long-term learning across releases.

---

## 2. MDSOC+ Optimization Architecture

### 2.1 Architecture Principle

The optimization subsystem follows the MDSOC+ pattern established project-wide (adopted 2026-04-17):

| Layer | Pattern | Optimization Role |
|---|---|---|
| **Kernel (ring 0)** | MDSOC only | No optimization runtime; static analysis only |
| **Compiler layers** | MDSOC capsule per layer | Layer 60 (MIR Opt), Layer 85 (MDSOC feature/optimization) |
| **Userland services** | MDSOC outer + ECS inner | Profile database entities, provider registries as ECS |
| **Apps** | MDSOC outer + ECS inner | Per-app optimization providers, session-local profiles |

### 2.2 Compiler Layer Mapping

The optimization pipeline maps onto the existing numbered compiler layers:

| Layer | Name | Optimization Responsibility |
|---|---|---|
| 00 | Common | DI slots for optimization config |
| 10 | Frontend | Syntax sugar optimization (desugar plugin kind) |
| 20 | HIR | Type-aware simplification (hir plugin kind) |
| 35 | Semantics | Lint: `mdsoc_plus_ecs_advisory.spl` for MDSOC+ conformance |
| 50 | MIR | MIR data, instructions, serialization |
| 55 | Borrow | Escape analysis facts for JIT (`escape.analyzed`, `escape.no_escape`) |
| 60 | MIR Opt | **Core optimization passes** — constant folding, DCE, CSE, GVN, inlining, loop opts, SIMD lowering, strength reduction, collection opt, target opt planning |
| 70 | Backend | Backend-specific passes (LLVM, Cranelift, WASM, CUDA, Vulkan), PGO instrumentation |
| 85 | MDSOC | Feature dimension: `feature/optimization/` — SIMD provider metadata, MirOptView entity view, ports |
| 90 | Tools | Perf tools: `profiler.spl`, `optimizer.spl`, API surface analysis |
| 95 | Interp | Interpreter execution, **tiered JIT manager** (`tiered_jit.spl`) |
| 99 | Loader | JIT context, JIT instantiator, module resolver |

### 2.3 MDSOC Feature Dimension for Optimization

The MDSOC layer (85) organizes optimization as a feature dimension:

```
src/compiler/85.mdsoc/feature/optimization/
├── __init__.spl
├── simd_provider.spl          # SIMD provider MDSOC metadata
└── app/
    ├── __init__.spl
    ├── optimize_input_port.spl  # Input port contract
    ├── optimize_output_port.spl # Output port contract
    └── ports.spl                # Port wiring

src/compiler/85.mdsoc/transform/feature/mir_to_optimizer/
├── __init__.spl
└── entity_view/
    ├── __init__.spl
    └── MirOptView.spl           # ECS entity view over MIR for optimization
```

This separation ensures optimization providers declare explicit port contracts and required facts, enabling the MDSOC checker to verify layer separation without importing backend types.

### 2.4 Optimization Plugin Contract

Established in `doc/07_guide/compiler_optimization_plugin.md`, the plugin system supports seven stages:

| Kind | Stage | Existing Source |
|------|-------|----------------|
| `syntax` | Frontend normalization | `src/compiler/10.frontend/` |
| `hir` | HIR simplification | `src/compiler/20.hir/` |
| `mir` | MIR optimization | `src/compiler/60.mir_opt/optimization_passes*.spl` |
| `pattern` | MIR pattern engine | `src/compiler/60.mir_opt/mir_opt/pattern_dispatch.spl` |
| `interpreter` | Interpreter runtime | `src/compiler/95.interp/` |
| `jit-hotspot` | JIT runtime planning | `src/compiler/95.interp/execution/tiered_jit.spl` |
| `backend-metadata` | Backend boundary | `src/compiler/70.backend/backend/optimization_passes.spl` |

Each plugin provides `OptimizationRuleProvider` metadata with:
- `required_facts`: preconditions that must be proven before the pass runs
- `produced_facts`: postconditions the pass guarantees
- `purity`: whether the pass is side-effect-free
- Capability gating (e.g., `["x86.aes", "x86.pclmul"]`)

---

## 3. Runtime HotSpot Optimization (Tiered JIT)

### 3.1 Current Implementation

The tiered JIT is implemented in pure Simple at `src/compiler/95.interp/execution/tiered_jit.spl` with the following tiers:

```
Tier 0: Interpreted (default)
  ↓ call_count >= tier1_threshold
Tier 1: Cranelift-compiled (fast compile, moderate runtime perf)
  ↓ call_count >= tier2_threshold
Tier 2: LLVM-compiled (slow compile, fully optimized runtime)
```

#### Core Types (existing)

```
enum JitTier:
    Interpreted    # Tier 0
    Fast           # Tier 1 (Cranelift)
    Optimized      # Tier 2 (LLVM)

struct FunctionProfile:
    name: text
    call_count: i64
    tier: JitTier
    compile_time_ms: f64
    source: text
    typed_mir: bool
    safe_deopt: bool
    hotspot_specialized_source: text
    hotspot_semantic_proof: bool
    var_facts: JitVarOptimizationFacts

struct TieredJitConfig:
    tier1_threshold: i64
    tier2_threshold: i64
```

### 3.2 Hotspot Plan Pipeline

The hotspot planning system is fact-driven (not heuristic). A function becomes eligible for optimization only when explicit proof facts are available:

```
Profile Collection
  ↓ profile.hot_count (call_count >= threshold)
Fact Gathering
  ↓ typed_mir (MIR is type-annotated)
  ↓ safe_deopt (deoptimization is safe)
Plan Construction
  ↓ JitHotspotPlan { eligible, facts, reason }
Provider Selection
  ↓ JitHotspotSpecializationProvider { semantic_proof }
Compile Decision
  ↓ JitHotspotCompileDecision { compile_source, provider_used }
Backend Choice
  ↓ JitHotspotRebuildChoice { selected_backend, cost_class }
```

#### Var Reassignment Optimization Facts

The var-reassignment hotspot path requires additional proof:
- `ssa.var_transform` — SSA conversion for reassigned variables
- `escape.analyzed` + `escape.no_escape` — stack/local assumptions verified
- `borrow.reassign_safe` — no outstanding borrows invalidated

Source: `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl` (SSA transform, phi planning, backend policy, provider factory), `var_reassign_analysis.spl` (raw analysis, JIT fact extraction).

### 3.3 Roadmap: Additional Tiers

| Tier | Status | Description |
|------|--------|-------------|
| Tier 0 (Interpreted) | **Implemented** | Fast startup, minimal memory, profile collection |
| Tier 1 (Cranelift) | **Implemented** | Baseline JIT via `rt_jit_*` externs (Rust bridge) |
| Tier 2 (LLVM) | **Planned** | Cost-gated (high compile cost), tier-2 threshold required |
| Tier 3 (Production) | **Roadmap** | Persistent profile + cross-version history → AOT-optimized SMF |

#### Tier 2 Cost Gating (existing policy)

LLVM rebuilds are explicitly cost-gated:
- Cranelift tier-1 rebuilds: medium cost, accepted immediately
- LLVM tier-2 rebuilds: high cost, deferred until tier-2 threshold AND LLVM backend available AND caller allows high compile cost
- `jit_hotspot_rebuild_choice` prefers LLVM only when all gates pass; falls back to Cranelift

### 3.4 Deoptimization

Optimized code assumptions may become invalid. The system supports safe deoptimization:

**Causes:**
- Module reload (hot code replacement)
- Library upgrade (ABI change)
- Hardware change (AVX512 → SSE4 fallback)
- Type feedback invalidation
- Profile corruption
- Borrow safety violation for var-reassignment optimizations

**Mechanism:**
- `jit_hotspot_plan_invalidate` marks a plan as invalidated
- `safe_deopt` fact must be proven before any optimization
- Missing `safe_deopt` rejects planning without dropping `hot_count` facts
- Fallback always preserves original (unoptimized) source path

---

## 4. MIR Optimization Passes

### 4.1 Current Passes (Layer 60)

Implemented in pure Simple at `src/compiler/60.mir_opt/`:

| Pass | File | Description |
|------|------|-------------|
| Constant Folding | `optimization_passes_part1.spl` | Evaluate constants at compile time |
| Copy Propagation | `optimization_passes_part1.spl` | Replace copies with originals |
| Dead Code Elimination | `optimization_passes_part1.spl` | Remove unreachable/unused code |
| Global Value Numbering | `optimization_passes_part2.spl` | Detect congruent expressions |
| Common Subexpression Elimination | `optimization_passes_part2.spl` | Reuse computed values |
| Inlining | `optimization_passes_part2.spl` | Inline small/hot functions |
| Loop Optimizations | `optimization_passes_part2.spl` | LICM, unswitching, unrolling |
| Outlining | `optimization_passes_part2.spl` | Extract cold paths to reduce code size |
| Strength Reduction | `optimization_passes_part1.spl` | `x * 2 → x << 1`, `% power_of_two → & mask` |
| Algebraic Simplification | `optimization_passes_part1.spl` | `x + 0 → x`, `x * 1 → x` |
| Peephole Optimization | `optimization_passes_part1.spl` | Local instruction combining |
| SIMD Lowering | `mir_opt/auto_vectorize_provider.spl` | Loop vectorization for contiguous data |
| Collection Optimization | `mir_opt/collection_opt_core.spl`, `collection_opt_patterns.spl` | Container-specific rewrites |
| Target Optimization | `mir_opt/target_opt_planner.spl` | Target-aware pass selection |
| SIMD Metadata | `mir_opt/simd_opt_metadata.spl` | SIMD target feature analysis |
| Pattern Dispatch | `mir_opt/pattern_dispatch.spl` | Idiom recognition engine |

### 4.2 Optimization Levels

Defined in `doc/07_guide/compiler_optimization_levels.md`:

| Level | Syntax | MIR | Native |
|-------|--------|-----|--------|
| `none` | — | — | `-O0` |
| `basic` | sugar desugar | const fold, DCE | `-O1` |
| `standard` | + normalize | + inline, CSE, GVN | `-O2` |
| `aggressive` | + all | + all passes | `-O3 -flto` |

### 4.3 Versioned Dynamic Optimizer Manifest

External plugins declare themselves via `.opt-manifest` files (design: `doc/05_design/optimizer_manifest_versioned_design.md`):

```
schema_version: 1
compiler_abi: "simple.opt.mir.v1"
name: "my-crypto-passes"
version: "0.3.1"
min_compiler_version: "0.9.0"
passes:
  - stable_name: "my_aes_fold"
    scope: "module"
    capability_requires: ["x86.aes", "x86.pclmul"]
    contract:
      inputs: ["typed_mir"]
      outputs: ["canonical_mir"]
      purity: "pure"
```

Registry types at `src/compiler/60.mir_opt/optimizer_manifest.spl`:
- `ManifestPassEntry`, `OptimizerManifest`, `ManifestError`
- `DynamicPassRegistry` — session-scoped, built-in passes always take precedence

---

## 5. Algorithm Provider Framework

### 5.1 Existing Provider Infrastructure

Simple already has provider selection at multiple levels:

#### Compiler-Level Providers

| Provider | Source | Selection |
|----------|--------|-----------|
| SIMD auto-vectorization | `src/compiler/60.mir_opt/mir_opt/auto_vectorize_provider.spl` | Target feature gating (`sse2`, `avx2`, `neon`) |
| MDSOC SIMD feature | `src/compiler/85.mdsoc/feature/optimization/simd_provider.spl` | MDSOC dimension metadata |
| Target opt planner | `src/compiler/60.mir_opt/mir_opt/target_opt_planner.spl` | Architecture-aware pass selection |

#### Runtime-Level Providers (stdlib)

| Provider | Source | Selection |
|----------|--------|-----------|
| BLAS | `src/lib/common/science_math/blas_provider.spl` | `BlasProvider` trait: Mock → CpuBlas → OpenBlas → cuBLAS |
| CUDA/cuBLAS | `src/lib/common/science_math/cuda_provider.spl` | `SIMPLE_BLAS_BACKEND` env var + waterfall probe |
| LAPACK | `src/lib/common/science_math/lapack_provider.spl` | Provider selection |
| GPU Graphics | `src/lib/gc_async_mut/gpu/session/optimization_provider.spl` | `GraphicsOptProvider` with per-target metadata |
| GPU Registry | `src/lib/gc_async_mut/gpu/session/optimization_registry.spl` | `GraphicsOptRegistry` — flat 4-slot registry |
| Rendering Opt | `src/lib/gc_async_mut/gpu/engine2d/rendering_opt_provider.spl` | Hit/miss/change counters per provider |
| SIMD variant | `src/lib/nogc_sync_mut/simd/variant_dispatch.spl` | ISA variant dispatch |

### 5.2 Provider Selection Pattern

The CUDA provider establishes the canonical selection pattern:

```
"auto" or "" → waterfall: CUDA if probe passes → CPU if probe passes → Mock

Provider hierarchy:
  Mock   — deterministic CPU stubs; always available
  Cpu    — OpenBLAS host backend; probe: openblas_available
  Cuda   — cuBLAS/cuSOLVER; probe: cuda_available AND device present
```

### 5.3 Graphics Optimization Provider Types

`GraphicsOptProvider` supports factory methods for:
- `shader_specialization(backend, arch)` — shader variant selection
- `pipeline_cache(backend, arch)` — PSO/pipeline cache
- `cpu_simd(arch, bits)` — CPU SIMD vectorization facts
- `cuda_kernel(arch)` — CUDA kernel specialization

Each provider stores: `provider_id`, `provider_kind`, `backend_kind`, `target_arch`, `target_bits`, `session_mode`, `policy_hash`, fact key/value pairs, and active/persistent flags.

### 5.4 Roadmap: Unified Algorithm Registry

Extend the existing provider pattern to a unified algorithm registry:

```
@algorithm("std.linalg.matmul")
fn matmul(...)

Providers:
  cpu.scalar     — always available
  cpu.simd       — probe: target_has_simd
  gpu.cuda       — probe: cuda_available
  gpu.vulkan     — probe: vulkan_available
  gpu.webgpu     — probe: webgpu_available
  gpu.metal      — probe: metal_available
  remote.cluster — probe: cluster_endpoint configured
```

Selection priority:
1. Manual override (`@use_provider("gpu.cuda")`)
2. Capability match (hardware probes)
3. Profile history (`.sprof` performance database)
4. Cost model (input shape → estimated time)
5. Fallback (always-available scalar)

### 5.5 Capability Detection

**CPU:** AVX2, AVX512, SSE2, NEON, SVE, RVV — already gated in `SIMDOptProvider.target_features`

**GPU:** CUDA, ROCm, Vulkan, WebGPU, Metal — session backends at `src/lib/nogc_sync_mut/gpu/engine2d/` (`cuda_session.spl`, `vulkan_session.spl`, `metal_session.spl`, `webgpu_session.spl`, `cpu_simd_session.spl`, `arm_riscv_session.spl`)

**Remote:** Cluster, Cloud, Distributed Runtime — future extension

### 5.6 Runtime Family Considerations

Each runtime family may provide different providers and cost models:

| Runtime | Provider Scope | Notes |
|---------|---------------|-------|
| Native | Full — CPU/SIMD/GPU/Remote | All backends available |
| Sandbox | CPU only | No device access |
| Browser (WASM) | WebGPU, CPU scalar | No CUDA/Vulkan |
| Embedded | CPU scalar, maybe SIMD | Memory constrained |
| Kernel | None | Static analysis only per MDSOC+ rules |

---

## 6. Persistent SMF Profile (`.sprof`)

### 6.1 New Files

```
module.smf         # Existing compiled module
module.sprof       # NEW: persistent profile database
```

### 6.2 Purpose

Store execution statistics, optimization decisions, and runtime feedback between runs:
- Call counts, self/total time per function
- Branch taken/not-taken ratios
- Loop iteration counts (min/max/avg)
- Inline cache hit/miss rates
- Provider selection history (which GPU/SIMD path was fastest)
- JIT tier transition history

### 6.3 SMF Integration

New sections for the SMF format (shared structural types at `src/compiler_rust/common/src/smf/`):

| Section | Purpose |
|---------|---------|
| `SMF_SECTION_PROFILE` | Symbol profiles, hotness, provider selection |
| `SMF_SECTION_MIGRATION` | Old hash → new hash mapping with confidence |

### 6.4 Cross-Version Profile Migration

| Match Level | Condition | Profile Reuse |
|-------------|-----------|---------------|
| Exact | Same MIR hash | 100% |
| Rename | Function renamed, body identical | 90% |
| Similar Body | Control flow graph similar | 50% |
| Signature Changed | Incompatible | 0% |

Migration report ties into the optimizer manifest versioning system, using `stable_name` identifiers for cross-version symbol identity.

---

## 7. Binary Optimization

### 7.1 LLVM PGO

Mapped to Simple's optimization levels (from `doc/07_guide/backend/llvm_optimization_workflow.md`):

| Simple Level | LLVM Flags |
|---|---|
| `none` | `-O0` |
| `basic` | `-O1` |
| `standard` | `-O2` |
| `aggressive` | `-O3 -flto` |

PGO workflow:
```bash
simple build --pgo-generate     # Stage 1: instrumented build
./app.exe <workload>            # Stage 2: collect .profraw
simple build --pgo-use          # Stage 3: profile-guided rebuild
```

### 7.2 BOLT Integration

Post-link optimization:
```
EXE → Profile Collection → BOLT → Optimized EXE
```

Improvements: function reordering, basic block reordering, ICache optimization, branch optimization.

### 7.3 IR Quality Checklist (existing)

From the LLVM workflow guide, verification before any backend change:
- Correct `nsw`/`nuw`/`noalias`/`nonnull` attributes (never invented for benchmark wins)
- Benchmark acceptance gate with before/after comparison
- Hot-path optimization pattern verification

---

## 8. Profiling Infrastructure

### 8.1 Existing Profiler Sources

| Component | Source |
|-----------|--------|
| Compiler profiler | `src/compiler/90.tools/perf/profiler.spl` |
| App profiler | `src/app/profiling/profile.spl`, `src/app/io/profiler_simple.spl` |
| Hotspot analyzer | `src/app/profiling/analyze_hotspots.spl` |
| SIMD profiler | `src/lib/nogc_sync_mut/simd/profile.spl`, `fp_profile.spl` |
| Engine profiler | `src/lib/nogc_sync_mut/engine/core/profiler.spl` |
| MDSOC adapter | `src/compiler/85.mdsoc/adapters/in/profiler_adapter.spl` |
| Rust runtime profile | `src/compiler_rust/compiler/src/runtime_profile/profiler.rs` |

### 8.2 Profile Data Model

```
FunctionProfile:
    call_count, self_time, total_time
    branch_taken, branch_not_taken
    loop_count (iterations, max, avg)
    deopt_count, jit_count
    inline_cache (target_count, miss_count)

Call Graph:
    caller → callee, count
    main ├─ parse: 50000
         ├─ execute: 30000
         └─ write: 20000
```

---

## 9. Optimize App (CLI Tool)

Existing CLI tool at `src/app/optimize/`:

| File | Purpose |
|------|---------|
| `main.spl` | Entry point |
| `analyze.spl` | Profile analysis |
| `compare.spl` | Before/after comparison |
| `apply.spl` | Apply optimization decisions |

Accessible via: `bin/simple optimize [analyze|compare|apply]`

---

## 10. Known Issues and Bugs

From `doc/08_tracking/bug/`:

| Bug | Date | Status |
|-----|------|--------|
| `jit_hotspot_optimization_plan_interpreter_cost` | 2026-05-28 | Interpreter cost model inaccurate |
| `jit_hotspot_shared_policy_plan_cost` | 2026-05-28 | Shared policy cost estimation |
| `jit_hotspot_verification_process_storm` | 2026-05-29 | Verification process storm under load |
| `optimize_native_cli_stub_segfault` | 2026-05-27 | Native CLI stub segfault |

---

## 11. Milestones

| Milestone | Description | Status |
|-----------|-------------|--------|
| M1 | Runtime Profile Infrastructure — call/loop/branch count, `.sprof` | **Partial** — `FunctionProfile` exists, `.sprof` file format TBD |
| M2 | Tiered HotSpot Runtime — Cold→Warm→Hot→VeryHot | **Implemented** — 3-tier (Interpreted/Fast/Optimized) with fact-driven planning |
| M3 | Persistent SMF Profiles — save/load/merge | **Planned** |
| M4 | Profile Migration — version diff, identity mapping, count reuse | **Planned** — manifest `stable_name` provides identity anchor |
| M5 | LLVM PGO — instrumentation + optimization | **Planned** — LLVM backend integration ready |
| M6 | BOLT Integration — post-link optimization | **Planned** |
| M7 | Unified Algorithm Provider Registry — CPU/SIMD/GPU/Remote | **Partial** — BLAS/CUDA/Graphics providers exist, unified registry TBD |
| M8 | Self-Learning Optimization — profile-guided runtime + compilation + algorithm selection | **Roadmap** |

---

## 12. Expected Benefits

| Category | Improvement | Mechanism |
|----------|-------------|-----------|
| Startup | 20–50% faster | Tiered JIT: interpret first, compile hot paths |
| Hot Loops | 2×–20× faster | Profile-guided inlining + LLVM tier-2 |
| SIMD Algorithms | 2×–16× faster | Auto-vectorization provider + target gating |
| GPU Algorithms | 10×–1000× faster | CUDA/Vulkan provider waterfall |
| Production Native | 10–30% faster | PGO + ThinLTO + BOLT |
| Long-Term Learning | Cumulative | Runtime knowledge preserved and migrated across releases |

---

## 13. Related Documents

### Research
- `doc/01_research/domain/optimization_plugin_jit_hotspot.md`
- `doc/01_research/domain/compiler_optimization_infra_refactor_2026-05-13.md`
- `doc/01_research/domain/llvm_optimization_best_practices_2026.md`
- `doc/01_research/domain/binary_size_optimization_across_languages.md`
- `doc/01_research/domain/target_instruction_optimization_32bit.md`
- `doc/01_research/local/bootstrap_size_optimization_research_2026-01-31.md`

### Design
- `doc/05_design/optimization_plugin_jit_hotspot.md`
- `doc/05_design/optimizer_manifest_versioned_design.md`
- `doc/05_design/target_instruction_optimization_32bit.md`
- `doc/05_design/baremetal_critical_app_profile.md`

### Guides
- `doc/07_guide/compiler_optimization_plugin.md`
- `doc/07_guide/compiler_optimization_levels.md`
- `doc/07_guide/backend/llvm_optimization_workflow.md`

### Architecture
- `doc/04_architecture/mdsoc_architecture_tobe.md` (Part 3: MDSOC+ ECS Business Layer)

### Plans
- `doc/03_plan/agent_tasks/optimization_plugin_jit_hotspot.md`
- `doc/03_plan/simple_db_jit_optimization_plan_2026-05-27.md`
- `doc/03_plan/render_2d_optimization_plan_2026-05-30.md`
- `doc/03_plan/simd_utf8_text_api_optimization.md`
