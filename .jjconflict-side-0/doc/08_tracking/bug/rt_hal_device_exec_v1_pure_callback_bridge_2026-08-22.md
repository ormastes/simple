# rt(hal) device exec V1 Pure callback bridge blocker

Date: 2026-08-22
Status: source bridge implemented; execution evidence remains release blocking

The additive IRQ/MMIO/DMA execution surface now has one frozen, caller-owned
21-argument ABI for eight fixed operations. The compiler can transactionally
rewrite its raw leaf to an exact direct or compare leaf, and the legacy
aggregate `*.safe.v1` planning APIs fail closed instead of being reported as
executed HAL.

The lifecycle/dispatch transport and prepare-time Pure-owned callback capsule
are now implemented. The native fixed-slot layer owns only generation handles,
leases, and callback retirement; device execution and comparison remain in
`RtHalDevicePreferredExecutionOwnerV1` / `RtHalDeviceComparisonOwnerV1`.
The bridge provides:

- fixed opaque storage and atomics only below the callback boundary;
- an explicit generation-bearing handle, with seal and shutdown;
- callbacks for configured, direct, and compare dispatch over caller pointers;
- no retained caller pointer and no callback registration after seal;
- parent-preferred physical execution exactly once, followed by captured replay
  in the C/Rust lanes;
- callback identity/lifetime proof so stale or foreign handles fail before an
  effect.

The source-current Pure compiler is unavailable, so the new exported callback
capsule has not yet been typechecked or linked end to end. Native/JIT use of an
`*.exec.v1` tag therefore remains unadmitted until the callback exports,
class-backed registry persistence, and all eight routed operations execute in
the matched cross-engine gate. This is not production-completion evidence.

Performance shape is fixed but not yet measurable end to end. Static direct
rewriting removes the configured-mode branch. Each wrapper is inline and adds
no collection, allocation, copy, scan, or dynamic lookup. The remaining work
must compare one matched source-current Pure baseline/after row and peak RSS;
the existing comparison-owner reference is 55.294 ns/provider, 1,536 KiB peak
RSS, and zero contract allocations.
