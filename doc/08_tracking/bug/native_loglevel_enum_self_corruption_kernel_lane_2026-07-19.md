# Native codegen: corrupted enum self in LogLevel.to_i64 — -kernel boot lane only

- **ID:** native_loglevel_enum_self_corruption_kernel_lane_2026-07-19
- **Status:** OPEN
- **Severity:** low-medium (16 recovered exception frames per -kernel boot; does
  NOT block desktop-ready; absent under OVMF)
- **Lane:** native-build (cranelift, x86_64-unknown-none), QEMU -kernel boots only

## Symptom
16 EXCEPTION FRAMEs per -kernel desktop boot, all identical shape:
rip=0x801234f (`rt_enum_check_discriminant`), ra in `LogLevel.to_i64`
(src/lib/.../failsafe/core.spl), cr2=0xf000f859f000e738 (corrupted pattern,
not null). All frames recover; `desktop-ready` and `first-frame-rendered`
still print. The SAME elf under OVMF pflash boots with ZERO exception
frames — the fault is specific to the -kernel boot path.

## Context
Observed 2026-07-19 during the glyph campaign's instrumented builds
(probe logging active). Likely the instance-method self-binding miscompile
class already noted this campaign (FontRenderConfig.identity() suspicion):
an enum method receives a corrupted `self` and the discriminant check
traps. May be probe-log-volume dependent; re-check with probes gated off.

## Repro
Guarded desktop build (glyph campaign recipe), boot via -kernel QMP harness
(session scratchpad boot_diag_wkheap.sh); grep serial for
`rt_enum_check_discriminant`. Compare same elf under OVMF harness: clean.

## Fix direction
Root-cause why enum-typed `self` differs between the two boot paths (likely
uninitialized state or memory-map difference the -kernel path exposes in
the log level filter). Verify whether it persists with probe logging gated
off before deeper work.
