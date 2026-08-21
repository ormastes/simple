# SimpleOS x86_64 Network Readiness Gate

Source: `test/03_system/os/simpleos_x86_64_network_gate_spec.spl`

Evidence classes: `source-contract` by default and `live-guest` only when
`SIMPLEOS_X64_SSH_QEMU=1` runs the production QEMU gate successfully.

## Scenarios

- Wire the bare-metal runtime to virtio packet initialization, TX, RX polling,
  and TX reclamation rather than device-presence markers.
- Arm TX before RX and require both packet directions before network-ready.
- Expose reusable network and SSH initialization from boot, route the SSH gate
  through it, and attach virtio-net to q35 QEMU lanes.
- When explicitly enabled, run the live x86_64 SSH QEMU gate. A disabled live
  lane is a visible skip and is not guest evidence.

