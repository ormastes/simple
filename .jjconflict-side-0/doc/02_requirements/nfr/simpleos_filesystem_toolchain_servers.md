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

