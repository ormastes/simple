# Virtual UART loses printable ASCII characters

Status: production repair passes the focused Phase 1 regression; pending release. Native/core qualification remains open.

`VirtualSerial.get_output()` called a local `char_from_code` table recognizing
only space, 0, 1, A, H, e, l and o. Every other printable character became `?`.
The previous H/Hello checks therefore passed while ordinary UART output was
corrupted.

Baseline: `build/phase-one-storage-gui-diagnostic/replay_vm_devices_spec/cycle-one.log`
reports 42 cases, 41 passed and one failed in 514 ms. The failed case writes
all 95 printable bytes through real MMIO, checks the exact TX buffer, and
compares output against a literal complete alphabet. The newline/control
policy regression passed independently.

Repair: `src/lib/nogc_sync_mut/replay/vm/devices/serial.spl` now imports the
existing pure `common.string_core.char_from_code(i64)` instead of maintaining
a partial local table. Printable-byte filtering, newline handling and raw TX
bytes are preserved. No SFFI or file I/O is added.

The selected cycle-two derivative and mapping are `build/phase-one-storage-gui-diagnostic/replay-uart-printable-cycle-two_spec.spl` and `build/phase-one-storage-gui-diagnostic/replay-uart-printable-cycle-two-mapping.sdn`.
Only the original failed case is selected; canonical source SHA-256 remains
`c455f2a4c125ae673f9ac3151c98218e3d5839ce1d6a42d9424f8fd8d63e1f97`. Cycle two passed only the original failed full-ASCII case: 1/1, 343 ms,
exit 0. Evidence is `build/phase-one-storage-gui-diagnostic/replay-uart-printable-cycle-two_spec/cycle-two.log`,
its resource/exit receipts and `uart-devices-cycle-two-inputs.sdn` (15 frozen
files verified before/after by the coordinator). Peak RSS was 210496 KiB;
the enforced-limit receipt reports quiescent=1.

The previous 41 passing cases were not rerun, and no full 42-case repaired-source
result is claimed. Production source SHA-256 is
`1dc71660a13cb7019bafa82eb13f9d30e8a2f9c739de79d14e336d9fe2a5503a`. Native and compiler/lib/MCP/LSP
verification remain open because no admitted pure-Simple full CLI is available.
