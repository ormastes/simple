# Unified CPU/GPU Containers & Algorithms Stdlib — CUDA (CCCL) Parity Research

**Phase:** 01_research · **Domain:** lib · **Topic:** gpu_containers_unified · **Date:** 2026-06-16
**Pipeline:** Research Step 1 (Claude). Hand off to `/research_codex` (Step 2) → `/arch`.

## User Request

> curent simple common algorithm and containers like cuda
> https://nvidia.github.io/cccl/unstable/libcudacxx/standard_api.html simple should
> supply equal or better in feature list. and it both support usage of cpu/gpu. research
> how organize with existing gpu api set. make them consistent and switchable by config.
> gpu least cuda provide std lib should provided and you can use cuda lib as backend when
> cuda is used. however, impl first cuda, then pure simple, then vulkan lib backed, metal
> backed. with veriety level of model like haiku, do jobs in pherallel but reviewed by
> opus verification after works. during this. find bug(include perf bug) fix and enhance
> simple(which is another goal)

## Goal Restatement (3 goals)

1. **Parity goal** — Simple's stdlib of common containers + algorithms must equal or exceed
   NVIDIA CCCL's feature list, usable on **both CPU and GPU**.
2. **Organization goal** — Fold this into the *existing* GPU API set (do not fork it),
   make backends **consistent and config-switchable**. CUDA, when present, is used as the
   backing library. Implementation order: **CUDA → pure-Simple → Vulkan → Metal**.
3. **Compiler/lang goal (co-goal)** — while doing the above, **find and fix bugs (incl.
   perf bugs) and enhance Simple itself.**

---

## 1. The Target: CCCL is THREE layers, not one

The linked page (`libcudacxx`) is only the **device-side STL** — *types*. The user's word
"algorithm" (reduce/scan/sort/transform) lives in the other two CCCL components. Parity
must be measured against all three:

| CCCL layer | What it provides | Maps to in Simple |
|---|---|---|
| **libcu++** (`cuda/std/*`) | Standard *types*: array, span, mdspan, optional, expected, tuple, complex, atomic, barrier, latch, semaphore, bit, bitset, numeric, ratio, random, chrono, type_traits | stdlib container/utility types |
| **Thrust** | Host/device *algorithms* with **execution policies** (`thrust::host` / `thrust::device` / `par` / `seq` / `par_unseq`) + iterators + vectors | the unified algorithm API + the **switch** mechanism |
| **CUB** | Block- / warp- / device-wide primitives (BlockReduce, WarpScan, DeviceRadixSort…) | low-level GPU kernel building blocks |

**Key insight (the spine of this whole effort):** Thrust's *execution policy* parameter is
exactly the "consistent and switchable by config" model the user wants. A single algorithm
call (`reduce(policy, data, op)`) dispatches to CPU or GPU by its policy argument. Simple
should adopt the same shape: one generic algorithm surface + an **execution-target**
parameter resolved from config/env.

### 1a. libcu++ header inventory (confirmed from indexed page)

Containers/utility: `array`, `span`, `inplace_vector` (C++26), `bitset`, `optional`,
`expected` (C++23), `tuple`, `functional`, `type_traits`, `utility`, `memory`,
`initializer_list`, `concepts`, `source_location`, `charconv`, `chrono`, `execution`
(partial). Also CCCL: `mdspan`/`mdarray`.
Atomics/sync: `atomic`, `barrier`, `latch`, `semaphore`.
Numerics: `bit`, `complex`, `numbers`, `numeric`, `ratio`, `random`, `limits`, `linalg`
(C++26), plus C-compat `cmath`, `cstdint`, `cstring`, `cfloat`, `climits`, `cstddef`.
Iterators/ranges: `iterator`, `ranges` (note: range **views and range algorithms are NOT
provided** by libcu++ — a gap even CUDA has).

### 1b. Thrust algorithm set (parity yardstick)

Transformations: `transform`, `for_each`, `fill`, `sequence`, `tabulate`, `replace`.
Reductions: `reduce`, `transform_reduce`, `inner_product`, `count`, `min_element`,
`max_element`, `reduce_by_key`. Scans: `inclusive_scan`, `exclusive_scan`,
`transform_scan`, `scan_by_key`. Sorting: `sort`, `stable_sort`, `sort_by_key`,
`is_sorted`. Reordering: `copy_if`, `remove_if`, `unique`, `partition`, `gather`,
`scatter`, `merge`, set operations. Searching: `find`, `binary_search`, `lower_bound`,
`upper_bound`, `equal_range`. Iterators: `counting`, `constant`, `transform`, `zip`,
`permutation`, `discard`, `reverse`.

---

## 2. Current Simple State (local research)

### 2a. Existing GPU API set (the thing to extend, NOT fork)

| Path | Role |
|---|---|
| `src/compiler/70.backend/gpu_portable_compute.spl` | One MIR → CUDA(PTX)/HIP/OpenCL/Metal/WebGPU emission. `PortableComputeTarget` enum. |
| `src/compiler/00.common/gpu_target_metadata.spl` | `gpu_target_metadata_default_backend_order()` → **"vulkan,metal,cuda,hip,opencl"** |
| `src/compiler/35.semantics/gpu_checker.spl` | `@gpu_kernel(target:…)` constraint validation; `GpuKernelTarget` Auto/Cuda/Hip/OpenCl/Vulkan/Metal/WebGpu |
| `src/compiler/70.backend/gpu_intrinsics.spl` | Thread/block IDs, barriers, atomics, **warp ops: shuffle/ballot/reduce/scan** (CUB-warp-level already exists!) |
| `src/compiler/70.backend/backend/{cuda_backend,vulkan_backend,vulkan_type_mapper}.spl` | PTX / SPIR-V codegen |
| `src/lib/gc_async_mut/gpu_ops.spl` | High-level API: `gpu_alloc/upload/download/launch/sync`; `GpuPtr`, `GpuModule`, `GpuLaunchConfig` |
| `src/lib/gc_async_mut/gpu/engine2d/{cuda,vulkan,metal,webgpu,cpu_simd}_session.spl` | Per-backend 2D sessions, dispatched by **`SIMPLE_2D_BACKEND`** env var |
| `src/lib/common/science_math/{blas,lapack,ndarray}.spl` + `blas_provider.spl` / `cuda_provider.spl` | **BLAS already switches CPU↔CUDA backend** — direct precedent for the policy model |

**Four backend-selection precedents already exist** (must be unified, not multiplied):
`SIMPLE_2D_BACKEND` env · `gpu_target_metadata` default order · `@gpu_kernel(target:)` ·
BLAS `blas_provider`/`cuda_provider`. The new compute policy should be one mechanism that
these all resolve through.

### 2b. Container / algorithm inventory + parity gaps

| Category | CCCL has | Simple has today | Gap |
|---|---|---|---|
| Fixed array | `array<T,N>` | builtin dynamic `[T]` only | no fixed-size `array<T,N>` |
| Span / view | `span`, `mdspan` | `ByteSpan` (`common/bytes/span.spl`, byte-only) | no generic `Span<T>`, no `mdspan` |
| Small/inline vec | `inplace_vector` | — | missing |
| Maps/sets | (not in libcu++) | `HashMap`,`BTreeMap`,`HashSet` (`nogc_sync_mut/collections/`) | **Simple ahead** here |
| Optional/Result | `optional`,`expected` | builtin `Option`/`Result` | parity |
| Tuple | `tuple` | builtin `(a,b,…)` | parity (no named `get<N>`?) |
| Bit / bitset | `bit`,`bitset` | — | missing |
| Complex | `complex` | NDArray numerics only | no scalar `complex<T>` |
| Atomics | `atomic` | **NONE** (actor model only) | missing — blocks CUB-style + lock-free |
| Barrier/latch/semaphore | yes | **NONE** | missing |
| Random | `random` | — | missing (engines + distributions) |
| Iterators/ranges | `iterator`,`ranges` | **no iterator protocol** | missing (+ blocked by bug, see §5) |
| Generic reduce/scan/sort/transform | Thrust | `array.sort()` builtin; search (`common/search/*`); **`gpu_*` are f32-only CPU stubs** | no generic, policy-driven algorithm layer |
| Warp/block primitives | CUB | warp shuffle/ballot/reduce/scan in `gpu_intrinsics.spl` | block-level cooperative ops not exposed |

**Stub-vs-real resolved (read `gpu_ops.spl:459-540`):** `gpu_reduce/scan/sort/map/filter/`
`gemm/dot/axpy` are *real working CPU implementations* but **f32-only, no execution policy,
no device dispatch** — they always run on CPU despite the `gpu_` name. This is itself a
**perf bug / misleading API** (see §5).

---

## 3. Proposed Organization (consistent + switchable)

A single new tier-default surface (lands in `nogc_async_mut` per the runtime-family ADR),
e.g. `std.compute` (names TBD in `/arch`), providing:

1. **Container types** to libcu++ parity: `Array<T,N>`, `Span<T>`, `MdSpan<T>`,
   `InplaceVector<T,N>`, `Bitset<N>`, `Complex<T>`, `BitOps`, `Atomic<T>`, sync types.
   Generic over `T` (today's `gpu_*` are f32-only — generics required).
2. **Algorithm surface** to Thrust parity: `reduce/scan/sort/transform/copy_if/unique/…`,
   each **generic** and taking an **execution policy**.
3. **CUB-equivalent primitives** as the kernel building blocks (extend `gpu_intrinsics.spl`
   warp ops with block-level cooperative reduce/scan).
4. **One execution-policy type** — `ExecTarget { Auto, Cpu, CpuPar, Cuda, Vulkan, Metal,
   PureSimple }` — resolved from config/env through a *single* resolver that subsumes the
   four existing precedents (§2a). Default runtime preference keeps the **landed**
   `vulkan,metal,cuda,hip,opencl → cpu` order; `Auto` honors it.
5. **CUDA-as-backend**: when target=Cuda and libcuda present, dispatch to CUDA (and, where
   it buys parity fast, Thrust/CUB via FFI) instead of re-deriving primitives.

### 3a. Two DIFFERENT orderings — keep them separate (do not conflate)

- **Implementation / delivery order (this initiative):** `CUDA → pure-Simple → Vulkan →
  Metal`. CUDA is built first because it doubles as the **reference oracle** (§4).
- **Runtime selection-preference order (already landed, unchanged):** `vulkan, metal, cuda,
  hip, opencl → cpu_simd → software → cpu`. This doc does **not** change that default.

These are orthogonal axes (build order vs runtime preference); the doc states both so it
reads as *consistent with* the landed `gpu_target_metadata` default, not contradicting it.

### 3b. Consistency with existing ADRs

- **"EXTEND `@gpu_kernel`/`gpu_portable_compute`, do not fork"** — algorithms compile down
  to `@gpu_kernel` bodies via the existing portable-compute MIR path. No new backend tree.
- **"`nogc_async_mut` is the default tier"** — the surface lands there first; `gc_async_mut`
  keeps the arena/torch-flavored GPU variant; `common/` holds the pure CPU reference.

---

## 4. Verification mechanism (makes "opus verifies" concrete)

The "haiku implements in parallel, opus verifies" instruction is realized as
**CUDA-as-oracle differential testing**, reusing the in-repo **dual-backend fail-closed**
pattern (`rt_exit 70`):

1. **CUDA cell** built first → becomes the oracle for each algorithm.
2. Every later backend (pure-Simple, Vulkan, Metal) must produce results that **match the
   CUDA oracle** — exact for integer/sort, **within tolerance** for float reductions whose
   summation order differs (must be specified, not bit-exact).
3. **Perf is measured against CUDA** (and against the CPU baseline; cf. the existing
   "GPU batch = ½ CPU baseline, 1 ms floor" model in `host_gpu_lane.md`). A backend slower
   than the CPU reference for a given size is a **perf bug** to file.
4. Fail-closed: a mismatch or missing-backend in strict mode exits non-zero (`rt_exit 70`),
   never silently degrades.

### 4a. Proposed parallel staffing plan (content only — NOT executed in Step 1)

- Decompose into a **grid of cells**: `{algorithm} × {backend}`. Each cell = disjoint file
  scope (required for parallel agents — see memory `feedback_parallel_scope_partition`).
- **Haiku** agents implement cells in parallel; **Opus** gate per cell = run differential
  test vs CUDA oracle + perf check + code review before merge.
- Wave order follows §3a delivery order: CUDA cells → pure-Simple → Vulkan → Metal.

---

## 5. Co-goal backlog — bugs & enhancements this work forces (REQUIRED section)

Surfaced by the agents / known from memory; each is a prerequisite or a perf risk:

| # | Item | Type | Why it blocks parity |
|---|---|---|---|
| B1 | `for x in <custom struct>` iterates **zero times** (no iterator protocol) | lang bug | blocks generic algorithms over custom containers/ranges |
| B2 | No generic `sort/reduce/fold` over arbitrary `T`; `gpu_*` are **f32-only** | feature gap | core of Thrust parity |
| B3 | `gpu_reduce/scan/sort` named "gpu" but **always run on CPU** | **perf bug** / misleading API | silent perf cliff; violates switchability |
| B4 | **No atomics / barrier / latch / semaphore** | feature gap | blocks CUB-style cooperative + lock-free containers |
| B5 | `f64` unreliable across interp/SMF/native (memory: `f64_unreliable_all_backends`) | **correctness+perf bug** | numeric algorithms need trustworthy f64 |
| B6 | array `.get(index>=1)` corruption (memory: `array_get_index_ge1_corruption`) | correctness bug | container indexing primitive |
| B7 | Four overlapping backend-selection mechanisms (§2a) | tech debt | "consistent + switchable" requires one resolver |
| B8 | Block-level cooperative reduce/scan not exposed (warp-level is) | feature gap | CUB block-tier parity |

These constitute the "enhance Simple" deliverable and should each get a bug/feature doc
during `/impl`.

---

## 6. Open questions for `/research_codex` (Step 2) and `/arch`

1. Namespace + naming for the unified surface (`std.compute`? `std.par`? `std.algorithm`?).
2. Should the execution policy be a **value argument**, a **type parameter**, or a
   **module-level config** (ambient `Auto` from env)? Thrust uses a value tag.
3. Link directly to **Thrust/CUB via FFI** for the CUDA cell, or only emit `@gpu_kernel`
   bodies? (FFI = fastest parity; kernel = fewer deps, reuses portable-compute.)
4. Float-reduction tolerance contract for differential testing (ULP? relative epsilon?).
5. How much of CCCL's *not-on-GPU* surface (chrono timezones, ranges views) to skip —
   "equal or better" need not mean copying CUDA's own omissions.

## 7. References (cross-links)

- `doc/05_design/compiler/gpu_design/gpu_backend_design.md` — GPU backend architecture
- `doc/04_architecture/lib/runtime_family_tier_defaults.md` — `nogc_async_mut` default tier ADR
- `doc/01_research/language/gpu_fpga/sycl_vs_simple_unified_accelerator_research_2026-06-13.md` — SYCL parity gaps G1–G12, unify strategy
- `doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md` — render offload patterns, backend dispatch
- `doc/01_research/ml/cuda/cuda_tbb_entry_compare.md` — CUDA vs TBB programming model
- `doc/06_spec/01_unit/compiler/codegen/gpu_portable_compute_spec.md` — one-MIR→multi-backend spec
- External: CCCL libcu++ Standard API (indexed `cccl-libcudacxx-standard-api`); Thrust execution policies; CUB device/block/warp primitives
