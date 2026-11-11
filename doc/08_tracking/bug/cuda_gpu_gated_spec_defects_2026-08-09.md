# CUDA/GPU defects uncovered by opening the P15 env gates (2026-08-09)

## Triage 2026-09-13
OPEN, out of scope for this lane: needs SIMPLE_CUDA_TEST=1 plus real CUDA
hardware to re-run the three gated specs this doc characterizes. The
embedded "HARNESS TRAP" finding (only the last failure in an it block is
reported) is a distinct, generic test-runner defect worth flagging to
whoever tracks test_runner_reports_only_last_failure_per_example_2026-08-04
(same shape), but reproducing the CUDA-specific findings needs a GPU host.
Left OPEN.

## Triage 2026-11-11 (p3fix-p2a-20261111 lane) — BLOCKED: needs seed rebuild + CUDA host; partial progress verified

Re-verified at release/1.0.0 tip (worktree @ 79d5af6723f6), source-only (this
host has no CUDA GPU; the tracked `bin/simple.exe` must not be rebuilt here):

- **Item 3 prerequisites landed.** The runtime dlopen table
  (`src/compiler_rust/runtime/src/cuda_runtime.rs:210,293`) now carries
  `cuDeviceGetAttribute`, and the `CudaFns`/`dispatch!` dlopen machinery is
  NOT feature-gated, so the not-cuda build can dispatch through it — the
  exact blocker this doc filed ("CudaFns has no cuDeviceGetAttribute entry")
  is gone. The rerouting itself is NOT done: the compiler shims in
  `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs` still contain
  exactly the filed 12 sentinel returns out of 38 total
  (`#[cfg(not(feature = "cuda"))] { Ok(Value::Int(-3)) }`, e.g.
  `rt_cuda_device_compute_capability_fn` at :1382-1393), and the runtime's
  own not-cuda stubs still return 0 (e.g. `rt_cuda_device_compute_capability`
  :1595) instead of dispatching through dlopen.
- **Item 4.2 landed.** `scripts/build/build_simple_audio_cuda_sffi.shs` now
  builds `libsimple_audio_cuda.so` (Linux/macOS/FreeBSD; staged under
  `build/sffi`, reached via LD_LIBRARY_PATH) — the "no build rule anywhere"
  state is over. Its header records this bug's date as the reason it exists.
- **Item 4.4 landed by rewrite.** `src/runtime/sffi/simple_audio_cuda_driver.c`
  is now a 166-line narrow ABI shim; the paired-i64 `_audio_write_u32s` path
  that overflowed odd element counts no longer exists — upload/download take
  explicit byte sizes (`simple_audio_cuda_upload/download`).
- **Item 4.3 still open** (readback root cause never isolated — needs GPU).
- Items 1/2 remain fixed per the 2026-08-09 record.

**Verdict: BLOCKED.** The remaining item-3 fix is a two-crate Rust-seed change
(compiler shims un-gated to call the dlopen-backed runtime externs; runtime
not-cuda stubs switched from hard 0 to dlopen dispatch) whose verification
requires rebuilding the Rust seed / self-hosted binary (the tracked
`bin/simple.exe` is frozen for parallel sessions) and then runtime-proving on
a CUDA host that the 12 calls return real values, not -3/0. Item 4.3 needs a
CUDA host outright. Neither is reachable from this bug lane's sanctioned
runtime (tracked seed binary, no CUDA).

**Grant requested (verbatim):** permission for a future lane to (a) rebuild
the Rust seed (or self-hosted native equivalent) at a NON-tracked output path
— e.g. `cargo build --release -p simple-compiler` with a scratch
`CARGO_TARGET_DIR`, or the sanctioned self-host native build — to verify the
item-3 rerouting, and (b) run the three `SIMPLE_CUDA_TEST=1` gated specs
(`gpu_ptx_gen_spec`, `feature/usage/cuda` internal-consistency spec,
`simple_audio_cuda_q15_env_spec`) on a CUDA GPU host with
`build_simple_audio_cuda_sffi.shs` deployed, to close item 3 end-to-end and
isolate item 4.3. The internal-consistency spec's `expected -3 to be greater
than 0` assertion is the ready-made regression oracle for item 3.

Status stays open. No code change in this lane.


Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Stream F1. Three gated specs were run with `SIMPLE_CUDA_TEST=1` (runner prints
the `test-env-gate: ... bypassing test daemon` line). Findings below; the fixed
items are noted for completeness, the rest are FILED, not fixed.

## 0. HARNESS TRAP: only the LAST failure in an `it` block is reported

Assertions do **not** abort the block, and the block counts as exactly **1**
failure whose message is the **last** failing assertion. Proven: appending
`expect("aaa").to_equal("bbb")` after an already-failing assertion changed the
reported message to `expected aaa to equal bbb` while `failed` stayed 1.

Consequence: **P15's one-line diagnoses are the LAST failure, not the cause.**
`simple_audio_cuda_q15_env_spec` was reported as "Q15 CUDA path yields 0"; the
real state was `reason == "cuda-unavailable"` with every sample 0 — the device
path never ran at all. Anyone triaging from a single message will misdiagnose.
Workaround used here: put the diagnostic assertion LAST. Note `print()` inside
library code is swallowed by the spec runner, so printf-debugging is unavailable.

## 1. FIXED — `gpu_ptx_gen_spec` expected PTX that does not exist

12 failures, of which only 2 were atomics. **The implementation was right and the
spec was wrong.** Verified with `ptxas` (CUDA 13.0.88), the authoritative oracle:

| PTX | ptxas verdict |
|---|---|
| `atom.global.add.u64` | VALID |
| `atom.global.add.s64` | **INVALID** — "Operation .add requires .u32 or .s32 or .u64 or .f64 or f16" |
| `atom.global.cas.b64` | VALID |
| `atom.global.cas.s64` | **INVALID** — "Unexpected instruction types specified for 'atom'" |
| `atom.global.min.s64` | VALID |

`atom.add` has no signed-64 form (two's-complement add is bit-identical, so
`.u64` is the only encoding); `atom.cas` is a pure bit compare and takes only
`.b32`/`.b64`. `ptx_builder.spl` is principled, not accidentally right: it
special-cases `I64 -> .u64` for add, routes and/or/xor/exch/cas through
`atomic_bit_type() -> .b64`, and lets min/max use the signed type. Spec
expectations corrected to `.u64` / `.b64`.

The other 10 were spec-vs-API drift, not atomics:
- 8x `variable LaunchConfig not found` — the class exists in
  `cuda_launcher.spl` and is exported; the spec simply never imported it.
- 2x `emit_call`/`emit_call_void` gained a required `arg_types` parameter and
  now emit ABI-correct `.param` staging (PTX calls must pass args through
  `.param` space). The spec still used the old signature and expected the old
  non-ABI text.

## 2. FIXED — `LaunchConfig.for_1d(n, 0)` divides by zero

Genuine implementation defect. `for_1d` computed
`(total_threads + block_size - 1) / block_size` with no guard, so a zero block
size trapped (`semantic: division by zero`) instead of yielding a config that
`validate()` rejects. Guarded in `for_1d` and `for_2d` (same latent bug in both
`block_w` and `block_h`).

The spec was ALSO wrong here, and self-contradictory: the test is named
"rejects zero block size" but asserted `expect(err).to_be_nil()` — i.e. that the
invalid config is valid. Assertion **strengthened** (not weakened) to require
the error and its exact text.

Result: `gpu_ptx_gen_spec` 69/81 -> **81/81**. Sabotage-verified: reverting the
`for_1d` guard and forcing `.s64` for add/cas re-failed exactly those 3 tests.

## 3. FILED — 12 CUDA interpreter shims have no dlopen fallback

This is the `expected -3 to be greater than 0` in `feature/usage/cuda`.
`-3` is not a CUDA driver code; it is the hardcoded
`#[cfg(not(feature = "cuda"))]` "not compiled in" sentinel in
`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`.

The deployed `bin/simple` is built WITHOUT the `cuda` feature and reaches the
GPU purely through the `get_cuda_dl()` / `cuda_dlopen::CudaFns` path. 26 shims
have that fallback; **12 do not** and therefore return the sentinel even though
libcuda is present and every neighbouring call succeeds:

`rt_cuda_device_compute_capability` (the failing one), `rt_cuda_ctx_destroy`,
`rt_cuda_memcpy_dtod`, `rt_cuda_module_load`, `rt_cuda_get_error_string`, and
the 7 compute ops `rt_cuda_f64_{binary_op,sum,minmax,sum_axis,scalar_div,slice_1d,slice_2d}`.

That is why `cuda_available()` is true and `cuda_device_get(0)` works while
`cuda_device_compute_capability` returns -3 — an internally inconsistent
surface, exactly what the spec's title ("internally consistent availability
state") is meant to defend.

**Not fixed here** because `CudaFns` has no `cuDeviceGetAttribute` entry, so the
fix means extending the dlopen table (typedef + optional field + symbol load)
and then rebuilding the shared `bin/simple`, which parallel sessions depend on.
Scoped as a deliberate follow-up rather than a rushed rebuild.

Secondary, in the `feature = "cuda"` build: `rt_cuda_device_compute_capability`
in `src/compiler_rust/runtime/src/cuda_runtime.rs` ignores both
`cuDeviceGetAttribute` return codes, so a failed query silently reports cc 0.

## 4. PARTLY FIXED — Q15 CUDA audio spec cannot reach the device

`simple_audio_cuda_q15_env_spec` had three stacked blockers:

1. **`.target sm_52` is rejected by CUDA 13** (Maxwell support dropped).
   `ptxas -arch=sm_52` fails with "Value 'sm_52' is not defined for option
   'gpu-name'"; the PTX body is otherwise valid and assembles cleanly at
   sm_75. This made `cuModuleLoadData` fail -> `cuda-audio-module-load-failed`.
   **FIXED**: target raised to `sm_75`, the lowest arch CUDA 13 accepts, and
   satisfied by both host GPUs (RTX A6000 cc 8.6, TITAN RTX cc 7.5).
   *Tradeoff, deliberately recorded*: this raises the floor from Maxwell to
   Turing. The properly correct fix is to derive `.target` from the device's
   compute capability rather than hardcoding either value; the narrow audio
   SFFI has no cc query today, so that is follow-up work.

2. **`libsimple_audio_cuda.so` has no build rule anywhere in the repo.**
   `DynLib.load("libsimple_audio_cuda.so")` has three consumers and the C
   source exists at `src/runtime/sffi/simple_audio_cuda_driver.c`, but nothing
   committed builds or installs it. The only copy on this host is an untracked
   artifact at `build/verify/simpleos-io-audio/`, not on the loader path, so
   the spec reports `cuda-unavailable` and silently exercises nothing. **The
   spec cannot pass from a clean checkout.** Needs a real build+deploy rule.

3. With the `.so` on `LD_LIBRARY_PATH` and the sm_75 fix, the spec now advances
   to `cuda-audio-readback-failed` — `launch`/`sync`/`download` in the C shim.
   Root cause not yet isolated; the prebuilt `.so` may also be stale relative
   to its C source. Open.

Also spotted while reading (not the cause of any failure, but a real overflow):
`_audio_write_u32s` writes in i64 pairs, so for an ODD element count it writes
one 8-byte word past the end of a `count*4` allocation — e.g. 16 bytes into the
12-byte `host_input` for a 3-sample input.
