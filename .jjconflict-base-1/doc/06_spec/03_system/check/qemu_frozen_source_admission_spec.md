# QEMU Frozen-Source Admission Contract

The x86_64 WM render/event producer and the ARM64 desktop producer may publish
QEMU acceptance artifacts only from a linked Git worktree with clean scoped
tracked/untracked roots. The fingerprint enumerates every consumed regular or
symlink input, including ignored generated sources, while the scoped Git check
also covers each producer and helper script. The producer records a sidecar
manifest containing the repository revision, dirty-state policy, entry and
source fingerprints, compiler hash, exact build command, and output hash.

The ARM64 QMP input checker cross-binds the frozen sidecar to the build
manifest's entry, compiler, source roots/fingerprint/count, build command, and
kernel hash; it rejects a missing, stale, or mismatched sidecar before it can
promote render or input evidence. Existing x86 render /
event, ARM QMP input, and x86/ARM SIMD acceptance rows remain active; this
contract adds source admission rather than replacing their capture assertions.

The x86 producer normalizes its deterministic generated log-config source
before admission and keeps it unchanged until publication, so a fresh linked
worktree has equal pre/post source fingerprints.

This specification is static-only. It does not start QEMU or invoke a native
build.
