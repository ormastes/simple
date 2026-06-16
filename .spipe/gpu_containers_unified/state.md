# Feature: gpu_containers_unified

## Raw Request
> curent simple common algorithm and containers like cuda
> https://nvidia.github.io/cccl/unstable/libcudacxx/standard_api.html simple should
> supply equal or better in feature list. and it both support usage of cpu/gpu. research
> how organize with existing gpu api set. make them consistent and switchable by config.
> gpu least cuda provide std lib should provided and you can use cuda lib as backend when
> cuda is used. however, impl first cuda, then pure simple, then vulkan lib backed, metal
> backed. with veriety level of model like haiku, do jobs in pherallel but reviewed by
> opus verification after works. during this. find bug(include perf bug) fix and enhance
> simple(which is another goal)

Goal command: `use spipe dec skill, complete doc/03_plan/lib/gpu_containers_unified/unified_compute_stdlib_rollout_2026-06-16.md`

## Task Type
feature

## Refined Goal
Add a single generic, config-switchable CPU/GPU compute surface to the `nogc_async_mut`
default tier — container/utility types at CCCL libcu++ parity plus a Thrust-parity
algorithm layer — that compiles through the existing `gpu_portable_compute`/`@gpu_kernel`
path (no fork), dispatches by one `ExecTarget` policy resolver, uses CUDA as backend and
differential-test oracle, and is delivered CUDA → pure-Simple → Vulkan → Metal while
fixing the prerequisite Simple bugs it depends on.

## Acceptance Criteria
- AC-1: One `ExecTarget { Auto, Cpu, CpuPar, Cuda, Vulkan, Metal, PureSimple }` resolver
  subsumes the four existing selectors (`SIMPLE_2D_BACKEND`, `gpu_target_metadata` order,
  `@gpu_kernel(target:)`, BLAS provider); `Auto` honors the landed
  `vulkan,metal,cuda,hip,opencl→cpu` order. Verified by an env/config selection spec.
- AC-2: A generic algorithm surface (transform, reduce, transform_reduce, inclusive_scan,
  exclusive_scan, sort, stable_sort, copy_if, remove_if, unique, partition, find,
  lower_bound, count, min/max_element, reduce_by_key) exists generic over `T`, replacing
  the f32-only `gpu_*` stubs. Each has an `it` block.
- AC-3: Container/utility types reach libcu++ parity: `Array<T,N>`, `Span<T>`, `MdSpan<T>`,
  `InplaceVector<T,N>`, `Bitset<N>`, `Complex<T>`, `Atomic<T>`, `Barrier`/`Latch`/
  `Semaphore`. Each compiles in interpreter and is usable in a `@gpu_kernel` body (CUDA).
- AC-4: The same algorithm call runs on CPU and on a GPU backend selected only by
  config/env (no source change). Proven by a discriminating spec (not just "a backend
  returned").
- AC-5: Every non-CUDA backend differential-passes the CUDA oracle — bit-exact for
  integer/sort/selection, within a declared float tolerance for reductions/scans;
  mismatch or strict-mode missing-backend exits fail-closed (`rt_exit 70`).
- AC-6: No `gpu_`-named function silently runs on CPU; a backend slower than the CPU
  reference for a target size is filed as a perf bug (NFR-3 honesty).
- AC-7: Co-goal bug backlog (B1 iterator protocol, B3 gpu_* CPU masquerade, B4 atomics,
  B5 f64 reliability, B6 array.get corruption, B7 four-resolver debt, B8 block-level
  cooperative ops) each has a tracked bug/feature doc; prerequisite fixes (P1–P5) land
  before the cell-grid waves.

## Scope Exclusions
- CCCL surface that is not GPU-relevant (chrono timezones, ranges views) may be deferred —
  "equal or better" need not copy CUDA's own omissions.
- This SPipe dev pass does NOT implement code; it formalizes goal + ACs and completes the
  rollout plan doc. Implementation runs the later SPipe phases per wave.

## Open Decisions (carry to arch phase)
- Q1: Namespace (`std.compute` / `std.par` / `std.algorithm`).
- Q3: CUDA cell = FFI to Thrust/CUB, or emit `@gpu_kernel` bodies (changes W1 effort).
- Q4: Float-reduction tolerance contract (ULP vs relative epsilon) — gates W2 float cells.

## Phase
dev-done

## Log
- dev: Created state file with 7 acceptance criteria (type: feature). Linked research
  (doc/01_research/lib/gpu_containers_unified/), requirements (FR + NFR drafts), and plan
  (doc/03_plan/lib/gpu_containers_unified/unified_compute_stdlib_rollout_2026-06-16.md).
