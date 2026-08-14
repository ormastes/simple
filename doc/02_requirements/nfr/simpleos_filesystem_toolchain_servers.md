# NFRs: SimpleOS filesystem toolchain and servers

- NFR-001: Load executable ranges with bounded memory; a 125 MiB compiler shall
  not require a 125 MiB contiguous kernel buffer.
- NFR-002: All wrappers shall fail closed on missing markers, guest failures,
  wrong provenance, timeouts, or stale artifacts.
- NFR-003: Network requests and query input shall be bounded and rejected when
  malformed; no marker-only success path is allowed.
- NFR-004: Reuse the existing VFS, ELF loader, TCP owner, Pure Simple database
  primitives, and install-image role lists; add no parallel abstraction.
- NFR-005: QEMU evidence shall record the exact kernel/image hashes, guest paths,
  serial transcript, request transcript, and exit codes.
## Restart12 deployment evidence NFRs (2026-08-14)

- NFR-SOS-TD-001: every admitted component and receipt is SHA-256 bound to its
  producer, validator, source revision, target identity, byte size, and path.
- NFR-SOS-TD-002: no historical artifact, host linker, fixed-command fixture,
  QEMU `-kernel`, `isa-debug-exit`, marker payload, or Rust seed can satisfy a
  deployment or live-execution criterion.
- NFR-SOS-TD-003: unavailable QEMU/physical capabilities remain BLOCKED with
  owner, reviewer, prerequisite, exact post-implementation resume command, and
  retained-artifact paths; QEMU never substitutes for a physical board.
