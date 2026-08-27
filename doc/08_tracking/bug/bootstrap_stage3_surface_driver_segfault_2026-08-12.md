# Bug: admitted Stage2 segfaults while parsing the Stage3 driver surface

Date: 2026-08-12  
Status: open, reproduced once  
Severity: release blocker

## Failure

The isolated `packed-memory-build8` full Cranelift bootstrap produced and
admitted its self-hosted Stage2 compiler, then the Stage3 native build exited
139. The retained Stage3 log ends immediately after releasing the entry surface
and starting the second source:

```text
phase2:surface:file:start .../src/app/cli/bootstrap_main.spl seq=1
phase2:surface:file:released .../src/app/cli/bootstrap_main.spl seq=1
phase2:surface:file:start .../src/compiler/80.driver/driver.spl seq=2
```

No source diagnostic, core receipt, or stack trace was retained.

## Authoritative evidence

- Stage2 admission receipt:
  `/mnt/data/bs2/packed-memory-build8/stage3/x86_64-unknown-linux-gnu/stage2-sanity.env`
- Admitted Stage2 SHA-256:
  `2a3ccce93e1d4f316d64194c732f0f7d759ea76d751bb33a9b226803e0dfebb5`
- Stage3 command transcript:
  `/mnt/data/bs2/packed-memory-build8/stage3/x86_64-unknown-linux-gnu/stage3-command.transcript`
- Stage3 log:
  `/mnt/data/bs2/packed-memory-build8/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
- Terminal milestone: `exit-139`

The admitted artifact exposes only `compile` and `native-build`; it is not a
full CLI and cannot qualify RISC-V unit/GHDL specs.

## Next diagnostic

Do not rebuild Rust authority or discard the Stage2/Stage3 caches. Reproduce
the exact transcript once under a retained core/backtrace wrapper, first with
the same streaming-surface settings and then—only if the first receipt proves
the crash owner—with streaming release disabled. Preserve the core, executable
hash, environment transcript, last surface identity, and stack trace. Treat
`driver.spl` as the first observed victim, not yet the proven source owner.
