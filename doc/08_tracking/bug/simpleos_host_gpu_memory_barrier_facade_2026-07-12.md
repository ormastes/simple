# SimpleOS host-GPU memory barrier facade
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

The freestanding ivshmem guest bridge directly imports `rt_memory_barrier` to
order payload writes before generation publication and receipt reads after
completion. Removing the fence would corrupt the protocol; the hosted
`app.io.volatile_ops` facade is not a valid baremetal dependency.

TODO: add the smallest fence operation to the existing SimpleOS MMIO owner,
route `host_gpu_ivshmem.spl` through it, and retain a focused ordering/link
gate for x86_64, AArch64, and RV64. Do not add a feature-local runtime shim.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
