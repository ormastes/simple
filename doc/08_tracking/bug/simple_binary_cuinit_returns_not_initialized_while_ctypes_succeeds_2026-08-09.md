# The Simple binary cannot reach CUDA at all: `cuInit` returns 3 while ctypes on the same host returns 0

**Filed:** 2026-08-09 (stream P7, native-tier device profile timing)
**Status:** OPEN — **pre-existing**, reproduced on unmodified `origin/main` (`bfd9284618a`)
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
