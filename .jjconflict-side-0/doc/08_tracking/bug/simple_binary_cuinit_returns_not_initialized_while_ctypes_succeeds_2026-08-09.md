# The Simple binary cannot reach CUDA at all: `cuInit` returns 3 while ctypes on the same host returns 0

**Filed:** 2026-08-09 (stream P7, native-tier device profile timing)
**Status:** NOT REPRODUCIBLE — retracted 2026-08-09 by stream P13 on origin/main `7f4004e1ff1` with the SAME binary (md5 d96f87a191403fd53aca879ee689ecdf). cuInit returns 0 and 2 devices enumerate under every lane; the fork hypothesis is refuted. See the retraction section at the end of this file.
**Severity:** high — it makes every "CUDA lane is green" result on this host unfalsifiable

## Symptom

On a host with two live NVIDIA GPUs, the Simple seed binary reports no CUDA at all:

```
$ ./bin/simple run probe.spl        # calls the rt_cuda_* externs directly
available=0        # rt_cuda_available()
init=3             # rt_cuda_init()      -> CUresult 3 = CUDA_ERROR_NOT_INITIALIZED
count=0            # rt_cuda_device_count()
device=-3          # rt_cuda_device_get(0)
event=-1           # rt_cuda_event_create()
```

The same host, same shell, same library, via Python ctypes:

```
$ python3 -c "import ctypes; l=ctypes.CDLL('libcuda.so.1'); ..."
cuInit rc= 0 cuDeviceGetCount rc= 0 count= 2
```

Host: NVIDIA RTX A6000 + TITAN RTX, driver 580.126.16, `/dev/nvidia{0,1,ctl}`
world-readable (`crw-rw-rw-`), Vulkan 1.4.312 sees both GPUs.

## This is NOT caused by the P7 change

Reproduced with the **unmodified** `origin/main` seed binary
(`/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple`,
29,577,536 bytes) as well as with the P7 rebuild. Identical output.

## Ruled out by measurement

* **Wrong library.** No — `strace -e trace=openat` shows the process resolving
  and opening the correct `/lib/x86_64-linux-gnu/libcuda.so.1`, byte-identical
  to the one ctypes loads successfully. `LD_LIBRARY_PATH` points at a
  `/usr/local/cuda-13.0/lib64` that does **not** contain `libcuda.so.1`
  (ENOENT), so the loader correctly falls through to the system copy. The stale
  `libcuda.so.535.247.01` sitting in the same directory is never opened (it
  returns 803 when loaded deliberately, not 3).
* **Wrong dlopen.** No — `dlopen("libcuda.so.1", RTLD_LAZY)` succeeds
  (`gpu.rs` `load_cuda`), and the fallback branch is not taken.
* **Wrong signature.** No — `type CuInit = unsafe extern "C" fn(u32) -> i32`
  (`gpu.rs:275`) matches the driver ABI, and it is called with flags `0`. A bad
  flag would be `CUDA_ERROR_INVALID_VALUE` (1), not 3.
* **Sandbox / device permissions.** No — reproduced identically with the
  harness sandbox disabled, and the Python probe succeeds from the *same*
  sandboxed shell.
* **`CUDA_VISIBLE_DEVICES`.** Unset.

## Leading hypothesis — NOT yet verified

**CUDA is fork-unsafe.** After `fork(2)`, driver calls in the child return
`CUDA_ERROR_NOT_INITIALIZED` (3) — exactly the code observed. `strace -f` of a
single `./bin/simple run` shows **7 distinct pids**, and `libcuda.so.1` is
opened in one of the children. The Python probe never forks and succeeds.

This is consistent with, but not proof of, the fork explanation: the trace was
not analysed to establish that the `cuInit` call itself happens in a process
descended from a fork that had already touched the driver. **Do not treat the
fork hypothesis as established.** The next step is to instrument
`rt_cuda_init_fn` to log `getpid()`/`gettid()` alongside the CUresult, or to
call `cuInit` from the parent before any fork and see whether the child
inherits a working context.

## Why this matters beyond CUDA

Every CUDA-lane spec on this host is passing through its **host-aware skip**,
not through a device. `cuda_vm_executor_conformance_spec` (2/2),
`cuda_exec_spec` (4/4) and the CUDA half of `conformance_suite_spec` (61/61)
are all green while `rt_cuda_available()` is 0 — so none of them can be
distinguished from a run on a machine with no GPU. That is a fail-open
measurement surface: a real CUDA regression would not turn any of them red
here. It also blocks the PROF-1 **Native** tier
(`src/lib/gc_async_mut/gpu_lane/cuda_native_profile.spl`), which correctly and
deliberately reports `Unavailable` rather than substituting a host clock.

## Fix direction

1. Confirm or refute the fork hypothesis as described above.
2. If confirmed, initialise CUDA lazily **in the process that will use it**, and
   never inherit a driver handle across `fork` — or re-`cuInit` in the child.
3. Independently: the CUDA-lane specs should assert *which* path they took, so
   "skipped because no device" can never be reported as the same green as
   "ran on a device". The P7 spec
   `test/01_unit/lib/debug/cuda_native_profile_spec.spl` does this — its
   live-device block asserts `cuda_native_events_available()` explicitly on
   both branches — but it is the exception, not the rule.

---

# 2026-08-09 — RETRACTED by stream P13: does not reproduce; fork hypothesis refuted

**Status change: OPEN -> NOT REPRODUCIBLE.** The headline claim ("the Simple
binary cannot reach CUDA at all") is **false on current `origin/main`**, and the
fork-unsafety hypothesis this doc left open is **refuted**, not merely unproven.

## Binary identity for every measurement below

```
readlink -f bin/simple -> bin/release/x86_64-unknown-linux-gnu/simple
29577536 bytes   mtime 2026-08-09 04:50:31 +0000
md5 d96f87a191403fd53aca879ee689ecdf
banner: "WARNING: this Rust-built Simple binary is a bootstrap seed only"
        "Simple Language v1.0.0-beta"
worktree: /home/ormastes/dev/pub/simple-p13-wt at origin/main 7f4004e1ff1
```

This is the **same 29,577,536-byte binary** this doc names at line 34, so the
contradiction is not a binary-identity difference.

## CUDA is reachable, under every lane tried

Probe calls the `rt_cuda_*` externs directly (top-level script form):

| Lane | `rt_cuda_available()` | `rt_cuda_init()` | `device_count()` | device 0 |
|---|---|---|---|---|
| `bin/simple run` (default) | **1** | **0** | **2** | NVIDIA RTX A6000 |
| `SIMPLE_EXECUTION_MODE=interpreter` | **1** | **0** | **2** | NVIDIA RTX A6000 |
| `SIMPLE_JIT=1` | **1** | **0** | **2** | NVIDIA RTX A6000 |
| `SIMPLE_JIT_STRICT=1` | **1** | **0** | **2** | NVIDIA RTX A6000 |

`cuInit` returns **0**, not 3, and **2** devices are enumerated, not 0.
**CUDA reachability is NOT lane-dependent** — the lane-dependence hypothesis the
coordinator raised is also refuted.

## The fork hypothesis is REFUTED

`strace -f` over a full `bin/simple run` of the probe:

- 7 distinct pids. Six are **threads** (`clone3` with
  `CLONE_VM|CLONE_THREAD|CLONE_SIGHAND`). Exactly **one** is a genuine `fork`
  (`clone(child_stack=NULL, flags=CLONE_CHILD_CLEARTID|SIGCHLD)`).
- Tracing `openat`, **all 20** `libcuda`/`/dev/nvidia*` opens occur in a single
  pid — the **main thread**, *not* the forked child.

So `cuInit` is not called in a forked child, and it succeeds. The fork is real
but is not on the CUDA path. Do not carry this hypothesis forward.

## The `libcuda` stub theory was tested and does NOT explain it either

The loader tries `/usr/local/cuda-13.0/lib64/libcuda.so.1` first (ENOENT) before
landing on the real `/lib/x86_64-linux-gnu/libcuda.so.1 -> libcuda.so.580.126.16`.
CUDA toolkits ship a **stub** `libcuda` that returns exactly
`NOT_INITIALIZED`/0 devices, which would fit this doc's symptom precisely.
It does not apply here: the four stub dirs on this host
(`/usr/local/cuda*/lib64/stubs/`) contain only `libcuda.so`, **never the soname
`libcuda.so.1`**, so the soname lookup can never select them. Forcing
`LD_LIBRARY_PATH=/usr/local/cuda-13.0/lib64/stubs` still yields
`avail=1 init=0 count=2`. Plausible mechanism, but **not** the one that fired.

## The unresolved `rt_cuda_event_create` extern is a real trap — but not the cause

`rt_cuda_event_create` (called in this doc's probe, line 17) is **not among the
34 `rt_cuda_*` symbols in the seed binary** — `strings` confirms 34 exports,
none of them `event_create`. Adding externs to Rust source does not change the
prebuilt seed, so that call was always going to fail.

Measured: an unresolved extern **aborts execution at that call and causes the
module to be re-run once** (JIT drops the whole module to the interpreter), but
it does **not** poison the sibling CUDA calls — they still returned
`avail=1 init=0 count=2 device=0`. So it explains this doc's `event=-1`, but it
does **not** explain `available=0 / init=3 / count=0`.

## What remains genuinely unknown

**Why P7 observed `available=0, init=3, count=0` on this host is unexplained.**
Same binary, same host, same driver, opposite result, and no mechanism tested
here reproduces it. Candidates NOT ruled out, in rough order of plausibility:
transient driver/host state at P7's measurement time; a different
`LD_LIBRARY_PATH`/`CUDA_VISIBLE_DEVICES` in P7's shell (`CUDA_VISIBLE_DEVICES=`
empty yields exactly count=0); GPUs held in exclusive-process compute mode by
another job. **What would settle it:** P7 re-running the probe with the env dump
(`env | grep -iE 'cuda|nvidia|ld_'`) and `nvidia-smi -q -d COMPUTE` captured in
the same shell, alongside the binary md5.

Until then this doc must NOT be cited as evidence that the CUDA lane is
unreachable, and no "CUDA lane is green" result on this host should be treated
as unfalsifiable on its account.

## Corollary defect found while testing (filed inline, see below)

Verifying the new `SIMPLE_REQUIRE_GPU` switch exposed a **separate, fail-open
defect**: env vars do not reach spec bodies under `bin/simple test`. See
`doc/08_tracking/bug/env_gated_spec_switches_are_inert_under_test_daemon_2026-08-09.md`.
