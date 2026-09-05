# Parallel Ownership

For Simple parallel code, the owner computes canonical state; children receive
copies, frozen snapshots, handles, scoped loans, or explicit moves; children
return newly created results; the owner validates and commits them.

Use `src/lib/common/structural/transfer/`, `storage_layout/`, and
`parallel_commit/` as canonical contracts. Do not transfer raw pointers across
safe process/device/remote boundaries. Dynamic index expressions overlap unless
range facts prove otherwise. Use bounded queues and deterministic parent commit
under critical policy. Keep logical `T[]` semantics separate from physical
AoS/SoA/AoSoA choices and pin ABI/wire/MMIO representations.

Verify source invalidation, cancellation, boundary isolation, replay order, and
logical layout parity. Do not advertise a common contract as runtime support
until the matching transport/runtime gate has executable evidence.
