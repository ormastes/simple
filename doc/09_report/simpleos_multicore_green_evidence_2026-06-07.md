# SimpleOS Multicore Green Evidence - 2026-06-07

## Scope

This report records the SimpleOS evidence for the multicore-green SPipe lane,
including the opt-in live QEMU green-carrier proof. It does not claim final
hardware context-switch handoff across APs; the live proof covers AP startup
plus scheduler-visible CPU1 green dispatch.

## Verified Commands

All commands were run from `/tmp/simple-cooperative-green`.

```sh
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_green_channel_wake_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple check src/os/kernel/scheduler/green_carrier.spl
./src/compiler_rust/target/debug/simple test test/01_unit/os/kernel/scheduler/green_carrier_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple check src/os/kernel/scheduler/scheduler.spl
./src/compiler_rust/target/debug/simple test test/01_unit/os/kernel/scheduler/scheduler_green_parallelism_spec.spl --mode=interpreter --clean
./src/compiler_rust/target/debug/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean
SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1 ./src/compiler_rust/target/debug/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean
```

## Results

| Evidence | Result | Assertions |
|----------|--------|------------|
| SimpleOS cooperative green | PASS | 3 |
| SimpleOS multicore green scheduler contract | PASS | 3 |
| SimpleOS green-channel wake bridge | PASS | 3 |
| SimpleOS green-carrier compile check | PASS | 1 file |
| SimpleOS green-carrier unit contract | PASS | 30 |
| SimpleOS scheduler compile check | PASS | 1 file |
| SimpleOS scheduler green-carrier parallelism | PASS | 4 |
| SimpleOS green-carrier QEMU spec default lane | PASS | 1 |
| SimpleOS green-carrier QEMU live lane | PASS | 1 |

## Notes

- The default QEMU spec lane proves the opt-in gate is wired and disabled unless
  `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1` is set.
- The live lane passed in 40469ms. The spec built the x86_64 probe, booted a
  two-CPU QEMU guest, and asserted both `[smp] AP reached 64-bit entry` and
  `[green-carrier-qemu] PASS=true` in serial output.
- The hosted SimpleOS specs prove scheduler-owned green execution state remains
  separate from normal OS task state.
- The green-carrier unit contract now proves requested-vs-active carrier
  parallelism is scheduler-owned and topology-bounded before final AP hardware
  handoff work.
- The scheduler green-carrier parallelism spec proves the real `Scheduler`
  stores that carrier limit, clamps it to topology, and preserves requested
  carriers across topology changes.
