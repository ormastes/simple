# riscv_services: probe status decoding and guards dropped by e274cd33719

- **Status:** open
- **Found:** 2026-11-21, Fable review of PR #10635 (riscv32 kernel link lane)
- **File:** `src/os/kernel/boot/riscv_services.spl`

## Symptom

Against `e274cd33719^1`, the stale-snapshot merge `e274cd33719` also removed,
and PR #10635 deliberately did not restore:

- `_decode_riscv_status(...)` around `rt_net_tx_test`, `rt_net_rx_ready` and every
  `rt_storage_*` probe. On riscv32 an `i32` error return widened into the `i64`
  ABI slot is positive, so the `< 0` failure checks never fire and a failed probe
  reads as ready.
- the PCI `count` bounds clamp (0..256) before the device loop;
- the failure branch on `boot_tcp_probe_close`'s return;
- `@unsafe` attributes and `pub` on `riscv_services_ready` / `riscv_network_ready`
  (no external importers found, so `pub` loss is not a break).

## Fix wanted

Re-apply the decode and the clamp on the current (post-b2cbe8871cf,
post-c06e8d5332c) shape of the file, with a spec that feeds a negative i32
status through the decode path on riscv32. Do not resurrect the removed
`_sffi_*` wrapper layer.
