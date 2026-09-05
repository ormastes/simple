# `use std.gpu.*` binds `rt_cuda_*` to the no-CUDA stub (device_count 0, cc (0,-3)) while direct module imports see 2 GPUs (2026-08-25)

**Status:** OPEN (seed dispatch defect, `src/compiler_rust`). **Binary:** Rust seed. **Host:** 2 live CUDA devices.

## Symptom
Same functions, different import path, different runtime binding:

| import | `gpu_device_count()` | `gpu_compute_capability(0)` |
|---|---|---|
| `use std.gc_async_mut.gpu_ops.*` (or `gpu_sffi`, `std.nogc_sync_mut.cuda.mod`) | **2** | (8, 6) |
| `use std.gpu.*` / `std.gc_async_mut.gpu.*` / `std.nogc_async_mut.gpu.*` (package `__init__`) | **0** | (0, **-3**) |

`-3` is the runtime's "built without the cuda feature" sentinel — but the same process, through
the direct import, reaches the real driver. No `use` warnings are emitted. `std.gpu_runtime`
standalone reports 2 (after the 2026-08-25 torch-gate fix).

## Impact
Every example and tutorial written against the documented `use std.gpu.*` surface silently
reports "no GPU" on a machine with two, and kernels launched through it write nothing
(`examples/08_gpu/simple_cuda_example/10.cuda_basic/12.First_Kernel` downloads all-0.0 while the
typed-transfer round-trip spec through the direct import passes 5/5).

## Reproduce (device-free discriminator: the -3 sentinel)
Two one-file probes in the scratchpad of the 2026-08-25 session (`p4` direct → 2, `p1` package →
0); minimal form:
```
use std.gpu.*
fn main():
    print "{gpu_device_count()} {gpu_compute_capability(0)}"     # 0 (0, -3)
```
vs. the same body with `use std.gc_async_mut.gpu_ops.*` → `2 (8, 6)`.

## Where to look
Package re-export resolution in the seed (`compiler_rust/compiler/src/interpreter_module/`) —
an `export use`/glob through `gpu/__init__.spl` apparently resolves the `extern fn rt_cuda_*`
declarations to a different (stub) provider than the direct module path does. Compare with
`runtime_native_gpu_stub.c` / `runtime_hosted_gpu_stubs.c` symbol precedence.
Unblocks the `use std.gpu.*` tutorial modules; until then examples import the concrete module.

## Correction (2026-08-25): this diagnosis is WRONG — not a dispatch defect

**Status: NOT A BUG in package import.** The heading, the table, and the "Where to look" section
above misattribute the cause. Superseded by
`doc/08_tracking/bug/deployed_binary_reads_stdlib_from_its_build_worktree_2026-08-25.md`.

The deployed binary reads `src/lib` from `/mnt/data/worktrees/parsefix-iso` — the worktree it was
built in — as well as from the tree you are working in, proven by strace (32 opens under the
foreign tree, 40 under the local one) and by 775 baked `parsefix-iso` strings in the binary.
`parsefix-iso`'s copy of `gpu_runtime/mod.spl` is the **pre-fix** version that gates on
`rt_torch_cuda_available()`. This host has CUDA but no PyTorch, so that probe answers false,
`gpu_available()` is false, device count is 0, and compute capability falls through to the `-3`
"no CUDA" sentinel. Every number in the table above is the old code's output, executed from
another tree.

So:
- The torch-gate fix (plan row 3) is correct and landed; nothing binds to a stub.
- `use std.gpu.*` vs. the direct module import differ only because they reach different files in
  the two trees, not because package re-export resolves externs differently.
- There is nothing to fix in `interpreter_module/` for this symptom, and
  `runtime_native_gpu_stub.c` symbol precedence is not involved.

What made the original diagnosis look solid was that the divergence was reproducible and
name-correlated. Four resolution hypotheses were tested and refuted before the cause was found —
stale `.smf` shadowing, a same-named class method colliding, the `torch.sffi` import, and module
caching. The test that settles it in one step is a **sentinel**: change the stdlib function to
return an impossible value and see whether it appears. It did not, which proves the file is not
being read and makes every resolution hypothesis moot.

Re-verify this symptom only with a binary built from the tree under test, or after checking
`strings -a <binary> | grep -c <other-worktree>`.
