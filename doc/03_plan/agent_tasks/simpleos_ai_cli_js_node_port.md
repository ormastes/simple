<!-- codex-design -->
# Agent Tasks: SimpleOS AI CLI JS/Node Port

## Completed In This Slice

1. Add contract-first architecture and detail design for the selected
   manifest-hardening path.
2. Implement `src/os/ai_cli_js_node_contract.spl`.
3. Add focused SPipe coverage in
   `test/system/os/simpleos_ai_cli_js_node_port_spec.spl`.
4. Add mirrored scenario manual evidence in
   `doc/06_spec/system/os/simpleos_ai_cli_js_node_port_spec.md`.

## Next Tasks Toward The Full Goal

1. Wire AI CLI manifests into SimpleOS package staging for x86 QEMU.
2. Add guest-side serial marker emission for runtime start, CLI smoke start,
   hardening denial, and blocker reporting.
3. Provision the smallest Node-compatible runtime artifact for x86, then repeat
   for RISC-V and ARM lanes.
4. Replace `pending` package/runtime pin fields with real package id, version,
   checksum, and runtime artifact identifiers.
5. Extend system specs from pure contract checks to QEMU guest execution checks
   once runtime artifacts exist.
