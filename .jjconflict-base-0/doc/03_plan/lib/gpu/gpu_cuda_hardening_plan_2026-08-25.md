# Plan: Simple GPU/CUDA programming hardening + tutorial + expressiveness (2026-08-25)

Goal (user): harden Simple CUDA/GPU programming; port `ormastes/cuda_exercise` into Simple under
`examples/` without duplicating the existing `ormastes/simple_cuda_example`; check Vulkan/Metal
with the same code under different config; md-embedded sdoctests; better MDSOC tests; keep
docs/guide/spec-docs current; **where the Simple GPU extension is not expressive enough, improve
Simple itself.**

Owner skill: `doc/00_llm_process/feature_expert/gpu_cuda_tutorial/skill.md`.
Guide: `doc/07_guide/lib/gpu_3d/cuda_gpu_programming.md`. Bugs: `doc/08_tracking/bug/*_2026-08-25.md`.

## Rules for this plan
- Evidence is attributed to a named binary. Two seeds exist on the box: the deployed
  `bin/simple` (05:16 redeploy, **cannot run `test`** — see bug) and the 08-23 seed at
  `/mnt/data/worktrees/goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple` used for all
  `test`/doctest evidence. Private verification build of `src/compiler_rust` goes to
  `/mnt/data/tmp/claude-1000/cargo-target-gpu` and is **never deployed over `bin/simple`**.
- Every fix ships a failing-pre-fix reproduce spec + neighbours. A correct spec that is RED on the
  deployed binary stays RED with a bug record.
- Land source only, as a plumbing-built commit on a **fresh** `origin/main` (not the stale shared
  tree), via `scripts/check/land.shs`.

## Status (§27-style — append a row per landed item)

| # | item | status | evidence |
|---|---|---|---|
| 1 | `std.io` cuda_sffi phantom ABI (17/24 externs nonexistent) rewritten to runtime ABI | DONE | `test/01_unit/lib/gpu/cuda_io_sffi_extern_abi_spec.spl` 6/6 |
| 2 | `gpu_ops` typed upload/download passed `Vec<Value>` ptr (SEGV ≥2048 f32) | DONE | `gpu_ops_typed_transfer_roundtrip_spec.spl` 5/5 (re-verified by coordinator) |
| 3 | `gpu_runtime` device probe gated on PyTorch → 0 GPUs | DONE | `gpu_runtime_backend_probe_spec.spl` 3/3 |
| 4 | `std.cuda` re-exports (`cuda_get_device_name`, `CudaStream` default stream) | DONE | `cuda_public_surface_spec.spl` 4/4; `examples/08_gpu/cuda/basic.spl` rc=0 on 2 GPUs |
| 5 | `std.gpu` `Context(Vulkan)` silently ran CUDA → `gpu_none()` | DONE | `gpu_context_vulkan_honesty_spec.spl` 3/3 |
| 6 | `cuda_jit_lane_executor` missing HIR `items` import | DONE (import) / OPEN (seed collision) | bug `cuda_jit_hello_lane_lower_module_missing_import_2026-08-25.md` |
| 7 | Same program, 3 backends via `simple.sdn` `gpu:` (`examples/08_gpu/backends/`) | DONE; Vulkan cases RED by design | `backends_spec.spl` 3/4 (+1 skip); 2 Vulkan bugs filed |
| 8 | Tutorial `simple_cuda_example` mounted at `examples/08_gpu/`, tiers 00/10/30 repaired | DONE | sweep: 11–19, 31–38 run 0 / spec green / md green |
| 9 | Tutorial tier 20 repair | DONE | 21 7/7, 22 8/8, 23 8/8, 24 10/10 (was 0/12), 27 8/8 real 2-GPU; 25/26 README-only + doctest; all run rc=0, all md green. Fixed `gpu_load_ptx` to use `rt_cuda_module_load_data_bytes` (NUL-terminated) — the un-terminated text span caused intermittent `CUDA_ERROR_INVALID_PTX` |
| 10 | Tutorial tiers 60/70/80 repair | DONE | 61 8/8, 62 8/8, 63 7/7, 64 9/9 (65/66 README-only), 71 9/9, 72 11/11, 73 8/8, 81 10/10, 82 10/10; every run rc=0, every README doctest 1/1 |
| 11 | MDSOC GPU layer/facet spec + `cross_query` import fix | DONE | `gpu_layer_facets_spec.spl` 9/9, `cross_query_spec.spl` 1/1 |
| 12 | Guide + `gpu_api.md` surface note + CHANGELOG + wiki skill + spipe-docgen spec docs | DONE | `cuda_gpu_programming.md` doctest 1/1 |
| 13 | Bug records: std.gpu package→stub (0,-3); Vulkan init under `run`; Vulkan after CUDA same process; top-level `arr[i]=` dropped; launch grammar no `stream:`; seed redeploy breaks `test` | DONE | 7 files |

## Phase E — improve Simple GPU expressiveness (ordered by cost/verifiability)

Finding that motivates it: in the interpreter, `k<<<grid: g, block: b>>>(args)` evaluates to
`Nil` (`compiler_rust/compiler/src/interpreter/expr/calls.rs:94`) — the language's own launch
syntax is a silent no-op; kernels are otherwise PTX text; the runtime has no streams/events/async
copies; CPU emulation is 1-D only.

| # | item | scope | acceptance | status |
|---|---|---|---|---|
| E0 | Establish what `<<<>>>` does on the native/JIT path (`native_project/discovery.rs`, HIR lowering arm) so the interpreter semantics match, not invent | read + 10-line probe with `SIMPLE_ENGINE_RECEIPT=1` on both engines | written finding in this plan | DONE — `KernelLaunch` has **no HIR lowering arm** (`hir/lower/expr/control.rs:2807` is only the identifier collector) and `native_project/discovery.rs:223` only visits sub-expressions; the interpreter returns `Nil` (`interpreter/expr/calls.rs:94`). So `<<<>>>` is a no-op in the interpreter and unsupported on native/JIT: E1/E3 define the semantics, nothing to match. Also: the shared tree's `src/compiler_rust` does not compile (other sessions' partial `import_loader.rs` edits) — the private build uses the clean origin-tip worktree. |
| E1 | 3-D CPU emulated launch in `gpu_ops` (`gpu_launch_emulated(grid, block, kernel)`; `gpu_block_id_{y,z}` / `gpu_local_id_{y,z}` / dims honoured) | pure Simple, no rebuild | spec: 2-D `matmul_tiled`-style index math matches CPU reference; tutorial 18/23/24 doctests can use it | DONE — `gpu_ops.spl` `_exec_*` state is now x/y/z, all 18 id/dim builtins read it, `gpu_launch_emulated(grid, block, kernel)` exported from `std.gc_async_mut.gpu`; `test/01_unit/lib/gpu/gpu_launch_emulated_3d_spec.spl` 3/3 on the 08-23 seed |
| E2 | Runtime streams / events / async copies: `cuStreamCreate/Destroy/Synchronize`, `cuEventCreate/Destroy/Record/Synchronize/ElapsedTime`, `cuMemcpyHtoDAsync/DtoHAsync`, `cuLaunchKernel` with `shared_bytes` + `stream` (`rt_cuda_launch_kernel_ex`) + `std.cuda` `CudaStream`/`CudaEvent` wrappers + `std.io` `cuda_launch_on(kfn, cfg, stream, args)` | Rust runtime (dlopen driver) + Simple wrappers; **requires seed rebuild** — verified on the private build only | spec (gated `SIMPLE_CUDA_TEST=1`): two streams overlap a copy and a kernel, event elapsed > 0, results correct; pre-flight RESOLVED: `extern-backing-census.shs:35` honours `SIMPLE_BIN`, so run the unbacked-extern ratchet at landing with `SIMPLE_BIN=/mnt/data/tmp/claude-1000/cargo-target-gpu/release/simple` (the private build that defines the new `rt_cuda_*`), and state that in the commit message; tutorial 22 rewritten to real overlap | DONE, VERIFIED ON THE DEPLOYED BINARY 2026-08-26 (see Redeploy verification below) — runtime `rt_cuda_stream_*`/`rt_cuda_event_*`/`rt_cuda_memcpy_*_async`/`rt_cuda_launch_kernel_ex` + `std.cuda` `CudaStream`/`CudaEvent` + `std.io` `cuda_launch_on`; `cuda_streams_events_spec.spl` 5/5 on the private build (2 streams really overlapped async copies + launches, events, 128 values correct), RED on every deployed seed until rebuild |
| E3 | Interpreter: `<<<>>>` no longer `Nil` — desugar to the E1 emulated launch when `gpu_ops` is imported, else a hard diagnostic `kernel launch requires std.gc_async_mut.gpu_ops in interpreter mode` | `compiler_rust` interpreter; seed-side | reproduce spec RED on deployed seed (bug record), green on private build; receipt-verified | DONE, VERIFIED ON THE DEPLOYED BINARY 2026-08-26 (5/5, was 0/5) — `KernelLaunch` now desugars to `gpu_launch_emulated` (int N → (N,1,1), 3-tuple passthrough) or errors `kernel launch `<<<>>>` requires `use std.gc_async_mut.gpu_ops.*` in interpreter mode`; `kernel_launch_syntax_interpreter_spec.spl` 0/5 on the 08-23 seed → 5/5 on the private build |
| E4 | Grammar `stream:` / `shared:` slots in `<<<…>>>` | both parsers + positional `KernelLaunch(Expr,Expr,Expr,[CallArg])` ripple in the self-hosted compiler | DEFERRED — `cuda_launch_on` from E2 expresses it; note the interim form in `kernel_launch_grammar_no_stream_slot_2026-08-25.md` | DEFERRED |

Exit criteria for Phase E: E1–E3 green on the private build with receipts, E2 honest about
"requires a rebuilt seed" in `gpu_api.md` and the guide, tutorial 22 demonstrates real overlap.

## Landing
1. Wait for tutorial agents (rows 9–10); final serial sweep with the 08-23 seed; commit + push
   the tutorial to `ormastes/simple_cuda_example` (restore its `.git` from the scratchpad first).
2. Re-fetch `origin/main`, rebuild the landing worktree at the fresh tip, copy only the files in
   `scratchpad/my_modified.txt` + new files, re-apply the CHANGELOG entry, add the submodule
   gitlink, run `land.shs`.

## Landing record (2026-08-25)

- Tutorial submodule `ormastes/simple_cuda_example`: commit `b58990d`, pushed and verified at
  origin (`e744055..b58990d`, `git ls-remote` confirms).
- simple-main commit `293d165139d` built by plumbing on the FRESH origin tip `b275bd0aac5`
  (67 files, +4800/-434), including the submodule gitlink at `b58990d` — the gitlink was
  declared in `.gitmodules` and `examples/FILE.md` but absent from the tree until now.
- Guard fix required by this landing: `check-no-conflict-markers-push.shs` ERRORed
  ("cannot read '<submodule>' … bad object") on **any** commit that adds a gitlink, because it
  `git show`s every non-deleted path as a blob. Now skips mode-160000 entries and reports the
  count in its verdict. Proven both ways on real fixtures: gitlink range → `PASS — 78 file(s)
  scanned … (1 submodule gitlink(s) skipped)`; a conflict marker added on top → `FAIL … (79
  file(s) scanned)`, so detection power is unchanged.
- Unbacked-extern ratchet: run with
  `SIMPLE_BIN=/mnt/data/tmp/claude-1000/cargo-target-gpu/release/simple` (the private build that
  defines the new `rt_cuda_*`), per `extern-backing-census.shs:35`.

## Redeploy verification (2026-08-26)

Rows E2 and E3 were "DONE (private build)" and blocked on a seed redeploy: landed code that no
deployed binary carried, so both specs were RED for users. The 2026-08-26 redeploy (built from
`origin/main`, deployed to `bin/release/x86_64-unknown-linux-gnu/simple`, previous binary kept as
`simple.pre-alwaysinline-20260826`) closes that. Measured on the deployed binary, 2-GPU host:

| spec | before | now |
|---|---|---|
| `kernel_launch_syntax_interpreter_spec.spl` (E3) | 0/5 | **5/5** |
| `cuda_streams_events_spec.spl` (E2) | RED, externs absent | **4/5** |

`nm -D` confirms `rt_cuda_stream_create`, `rt_cuda_event_record`, `rt_cuda_memcpy_htod_async` and
`rt_cuda_launch_kernel_ex` are all defined in the deployed binary.

**Both E2 hardware scenarios pass** — "overlaps two async uploads + kernels on two streams, timed
by events" and "creates a non-blocking stream and a launch on the default stream still works".
Real two-stream overlap with event timing works on real hardware. That was E2's exit criterion.

### The remaining 1/5, left RED deliberately

`declares every E2 extern with the runtime's arity` fails with
`rt_cuda_stream_create: not defined in runtime, ...`. This is **not** a stale spec or a checker
artifact: those symbols are defined only in the **Rust** runtime
(`src/compiler_rust/common/src/runtime_symbols.rs`) and in **no** file under `src/runtime/`, the C
runtime. So the E2 surface is unavailable to any lane linking the C runtime rather than the Rust
one, and the spec is correctly reporting that. Verified by grep rather than assumed — the hardware
scenarios passing made a stale-spec explanation tempting, and it is wrong.

Left RED per `.claude/rules/testing.md` ("a correct spec that fails is a legitimate artifact");
weakening it would hide a real portability gap. Unblock condition: implement the E2 `rt_cuda_*`
entry points in the C runtime (the honest fix), or scope the arity check to the Rust lane *and*
file the C-lane gap separately.
