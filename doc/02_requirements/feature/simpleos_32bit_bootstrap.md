# SimpleOS 32-bit bootstrap requirements

- REQ-001: One shared API shall describe x86_32, ARM32, and RV32 target triples, ABI, linker emulation, sysroot/tool manifests, and QEMU executors.
- REQ-002: Phase 1 and Phase 2 shall have distinct artifact hashes and explicit parent lineage.
- REQ-003: Acceptance shall bind the host compiler, target metadata, sysroot, linker script, tool manifest, and QEMU transcript.
- REQ-004: Unavailable execution shall fail closed and remain resumable per target.
- REQ-005: Promotion shall require an Ed25519 signature from the configured
  trusted key plus caller-supplied expected receipt ID and nonce, so replayed
  evidence cannot be admitted by serial text alone.

These requirements directly restate the user-selected scope; no alternative options remain pending.
