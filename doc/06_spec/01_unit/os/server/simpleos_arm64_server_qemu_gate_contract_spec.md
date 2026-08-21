# SimpleOS ARM64 Server QEMU Gate Contract

Source: `test/01_unit/os/server/simpleos_arm64_server_qemu_gate_contract_spec.spl`

Evidence class: `source-contract`.

## Scope

The scenarios validate that the ARM64 server wrapper requires a filesystem
artifact, guest-observed launch markers, protocol output, and bound evidence.
They do not convert a wrapper self-test or host fixture into a live-guest pass.

Production gate: `scripts/check/check-simpleos-arm64-servers-qemu.shs`.

