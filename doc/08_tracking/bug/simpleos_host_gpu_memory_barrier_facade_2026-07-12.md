# SimpleOS host-GPU memory barrier facade
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

The freestanding ivshmem guest bridge directly imports `rt_memory_barrier` to
order payload writes before generation publication and receipt reads after
completion. Removing the fence would corrupt the protocol; the hosted
`app.io.volatile_ops` facade is not a valid baremetal dependency.

TODO: add the smallest fence operation to the existing SimpleOS MMIO owner,
route `host_gpu_ivshmem.spl` through it, and retain a focused ordering/link
gate for x86_64, AArch64, and RV64. Do not add a feature-local runtime shim.

