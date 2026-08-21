# SimpleOS 32-bit bootstrap NFRs

- NFR-001: Shared validation logic must avoid per-architecture validator copies.
- NFR-002: A fabricated final marker, zero hash, wrong ABI/QEMU tuple, incomplete phase, or mismatched lineage must be rejected.
- NFR-003: Host-independent checks must not launch QEMU, build a compiler, or claim target-native success.
- NFR-004: Every SHA-256 field uses the canonical lowercase-hex validator;
  length-only and uppercase/non-hex digests are invalid.
