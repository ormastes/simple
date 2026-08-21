# SimpleOS 32-bit bootstrap receipt contract — operator manual

Source: `test/01_unit/os/port/simpleos_32bit_bootstrap_contract_spec.spl`

Status: host-independent contract implemented; live x86_32, ARM32, and RV32 rows are BLOCKED by Todo 834-836. This manual makes no bootstrap, QEMU, or target-native PASS claim.

## Operator flow

1. Inspect the shared profiles for canonical triple, ABI, linker emulation, manifest paths, and QEMU executable.
2. Validate distinct Phase 1/2 hashes, Phase 2 parent lineage, no-stub mode, and nonzero sysroot/linker/tool hashes.
3. Require one nonce of at least 16 characters in `guest-entry`, filesystem execution, `reap exit=37`, and `TEST PASSED` markers.
4. Treat any missing or mismatched field as FAIL. Treat unavailable QEMU execution as BLOCKED.
5. Before promotion, require the expected receipt ID and nonce and verify the
   canonical signing bytes with the configured Ed25519 key. Structural validity
   alone is never acceptance authority.

## Traceability

- REQ-001: profile scenario.
- REQ-002/REQ-003: complete and negative receipt scenarios.
- REQ-004: target-native v1 remains fail-closed and Todo resume rows stay open.
- REQ-005: malformed digest, absent key identity, replayed receipt ID, and
  replayed nonce regressions fail closed.
