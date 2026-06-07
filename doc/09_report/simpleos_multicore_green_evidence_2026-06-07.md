# SimpleOS Multicore Green Evidence - 2026-06-07

## Scope

This report records the fast SimpleOS evidence for the multicore-green SPipe
lane. It does not claim final hardware context-switch handoff across APs; that
remains covered by the opt-in QEMU live lane in
`test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl`.

## Verified Commands

All commands were run from `/tmp/simple-cooperative-green`.

```sh
bin/release/simple test test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl --mode=interpreter --clean
bin/release/simple test test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl --mode=interpreter --clean
bin/release/simple test test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl --mode=interpreter --clean
bin/release/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean
```

## Results

| Evidence | Result | Assertions |
|----------|--------|------------|
| SimpleOS cooperative green | PASS | 3 |
| SimpleOS multicore green scheduler contract | PASS | 3 |
| SimpleOS green-channel wake bridge | PASS | 3 |
| SimpleOS green-carrier QEMU spec default lane | PASS | 1 |

## Notes

- The default QEMU spec lane proves the opt-in gate is wired and disabled unless
  `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1` is set.
- The live lane, when enabled, must build the x86_64 probe, boot a two-CPU QEMU
  guest, and find both `[smp] AP reached 64-bit entry` and
  `[green-carrier-qemu] PASS=true` in serial output.
- The hosted SimpleOS specs prove scheduler-owned green execution state remains
  separate from normal OS task state.
