# QEMU Frozen-Source Admission Contract

The x86_64 WM render/event producer and the ARM64 desktop producer may publish
QEMU acceptance artifacts only from a linked Git worktree with clean scoped
source roots (including untracked files). The producer records a sidecar
manifest containing the repository revision, dirty-state policy, entry and
source fingerprints, compiler hash, exact build command, and output hash.

The ARM64 QMP input checker rejects a missing, stale, or output-mismatched
sidecar before it can promote render or input evidence. Existing x86 render /
event, ARM QMP input, and x86/ARM SIMD acceptance rows remain active; this
contract adds source admission rather than replacing their capture assertions.

This specification is static-only. It does not start QEMU or invoke a native
build.
