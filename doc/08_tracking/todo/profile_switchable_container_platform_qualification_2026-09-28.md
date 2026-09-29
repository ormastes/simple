# Profile-switchable container algorithms: platform qualification

Status: OPEN

This tracks the remaining item 7 work after PR #1830. The implementation
status is FAIL, so landing that PR is not completion evidence. The owning
requirements are `doc/02_requirements/feature/profile_switchable_container_algorithms.md`
and the acceptance plan is
`doc/03_plan/sys_test/profile_switchable_container_algorithms.md`.

## Shared implementation gate (TODO 341)

Finish typed collection planning and MIR selection, all applicable P6 metrics,
generic key/value coverage, guarded `--explain-collection-plan` output, and
profile admission/cache invalidation. Execute the item 7 SPipe and integration
specs with an admitted, source-matched pure-Simple CLI. Record the compiler
source identity and binary SHA-256. A Rust bootstrap seed is diagnostic evidence
only. Keep this gate open until REQ-PSC-001 through REQ-PSC-008 and
NFR-PSC-001 through NFR-PSC-005 have executable evidence.

## macOS (TODO 342)

On a macOS host, run the admitted compiler's interpreter and supported native
backends against the same attributed set/map fixtures. Capture and replay a
target-matched `.sprof`; prove per-instance auto/forced selection, semantics,
wrong-target rejection, and source/cache invalidation. Retain scaling, allocation,
warm latency, and peak RSS receipts for the macOS target. Record unsupported
backends explicitly instead of reporting them as passes.

## Linux (TODO 343)

On a Linux host, run the same source-matched interpreter/native differential and
capture/replay gates, including generic keys, collision pressure, and wrong-target
rejection. Retain scaling, allocation, warm latency, and peak RSS receipts with
the target triple and binary SHA-256.

## Windows (TODO 344)

On a Windows host, run the admitted compiler's supported interpreter, JIT, and
native paths against the attributed fixtures. Prove profile capture/replay,
per-instance isolation, semantic parity, target mismatch rejection, and the
NFR scaling/memory/latency gates. Record any unsupported backend as such.

## FreeBSD (TODO 345)

After a source-matched FreeBSD toolchain is admitted, run the applicable
interpreter/native item 7 gates in FreeBSD or the canonical QEMU guest. Prove
target-specific profile admission and semantics; retain the target, binary
identity, command/status, timing, memory, and log receipts. This is separate
from the existing general FreeBSD bootstrap TODO 319.

## SimpleOS and remaining supported targets (TODO 346)

For each supported SimpleOS target/backend, run the attributed collection
fixtures in an executable target or QEMU environment, then verify the same
semantic and profile-selection contract. Capture target identity and a
cross-target rejection case. Add any other supported target to the evidence
matrix before closing this row; label targets without an executable backend
as unsupported rather than passed.

Closing any platform row requires the shared implementation gate and retained
evidence for that platform. No platform row is marked complete by PR #1830.
