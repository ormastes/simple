# SimpleOS ARM64 Server QEMU Gate Contract

Source: `test/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.spl`

Evidence class: `source-contract`.

## Scope

The scenarios validate that the ARM64 server wrapper requires a filesystem
artifact, guest-observed launch markers, protocol output, and bound evidence.
They do not convert a wrapper self-test or host fixture into a live-guest pass.

The gate must also treat every image carrying a database credential as
sensitive and destroy it after both normal and crash-recovery boots. Target
evidence is accepted only when the canonical guest zeroization routine ran,
both boot transcripts are bound by nonzero SHA-256 values, and the retained
artifacts contain neither credential bytes nor uncleared hash workspaces.
Source-side cleanup or deleting only the host image is not target-zeroization
evidence.

Production gate: `scripts/check/check-simpleos-arm64-servers-qemu.shs`.
