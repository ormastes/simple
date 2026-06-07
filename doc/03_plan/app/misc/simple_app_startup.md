# Simple App Startup — System Test Plan

## Scope

This plan covers startup policy for native, interpreter script, SMF, and
SimpleOS launcher paths.

Covered:

- launch-kind detection for native/script/SMF entries
- argv normalization for direct file launch
- capability-gated arg parser, mmap/cache, and dynlib startup inclusion
- native dynlib and role-2 SMF dynlib dependency policy
- explicit SimpleOS launch metadata and VFS prewarm policy
- SimpleOS WM hover prefetch of executable/SMF bytes without execution
- SimpleOS WM hover miss materialization through VFS/rootfs read-ahead into the
  app registry
- embedded SMF `.launch_meta` rendering and parsing
- embedded native `SIMPLE_LAUNCH_V1` trailer rendering and parsing
- build-emitted launch metadata sidecar rendering and parsing as auxiliary check input

Excluded:

- live macOS `.dylib` acceptance evidence
- process-callable SimpleOS shared-library mapping
- platform-native section variants for ELF, Mach-O, and PE launch metadata

## Execution

Run executable specs from `test/` only:

- `test/03_system/app/simple/feature/simple_app_startup_spec.spl`
- `test/03_system/app/simpleos/feature/simple_app_startup_spec.spl`
- `test/02_integration/app/startup_argparse_mmap_perf_spec.spl`

Generated/manual docs mirror the executable paths:

- `doc/06_spec/test/03_system/app/simple/feature/simple_app_startup_spec.md`
- `doc/06_spec/test/03_system/app/simpleos/feature/simple_app_startup_spec.md`

## Pass Criteria

- All specs use real assertions and built-in matchers only.
- Direct launch args are normalized without duplicate argv zero.
- Mmap/cache strategy is selected only when metadata requests it and the
  platform supports a cache lane.
- Dynlib loader is included only when native or SMF dynlib dependencies are
  declared.
- SimpleOS hover prefetch records/warm-checks executable bytes, uses VFS to
  materialize bytes on cache miss when available, and does not launch a process.
- `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`.

## Traceability

| REQ | Description | Executable Spec | Generated Spec | Coverage |
|-----|-------------|-----------------|----------------|----------|
| REQ-001 | Launch kind detection | `test/03_system/app/simple/feature/simple_app_startup_spec.spl` | `doc/06_spec/test/03_system/app/simple/feature/simple_app_startup_spec.md` | Full |
| REQ-002 | File arg parsing and parser gating | `test/03_system/app/simple/feature/simple_app_startup_spec.spl` | `doc/06_spec/test/03_system/app/simple/feature/simple_app_startup_spec.md` | Full |
| REQ-003 | Mmap/cache startup strategy | `test/03_system/app/simple/feature/simple_app_startup_spec.spl` | `doc/06_spec/test/03_system/app/simple/feature/simple_app_startup_spec.md` | Full |
| REQ-004 | Conditional native/SMF dynlib loading | `test/03_system/app/simple/feature/simple_app_startup_spec.spl` | `doc/06_spec/test/03_system/app/simple/feature/simple_app_startup_spec.md` | Full |
| REQ-005 | Build launch metadata sidecar | `test/03_system/app/simple/feature/simple_app_startup_spec.spl` | `doc/06_spec/test/03_system/app/simple/feature/simple_app_startup_spec.md` | Full |
| REQ-006 | Embedded SMF launch metadata | `test/03_system/app/simple/feature/simple_app_startup_spec.spl` | `doc/06_spec/test/03_system/app/simple/feature/simple_app_startup_spec.md` | Full |
| REQ-007 | Embedded native launch metadata | `test/03_system/app/simple/feature/simple_app_startup_spec.spl` | `doc/06_spec/test/03_system/app/simple/feature/simple_app_startup_spec.md` | Full |
| REQ-100 | SimpleOS launch metadata and VFS prewarm | `test/03_system/app/simpleos/feature/simple_app_startup_spec.spl` | `doc/06_spec/test/03_system/app/simpleos/feature/simple_app_startup_spec.md` | Full |
| REQ-101 | SimpleOS hover prefetch and VFS miss warmup | `test/03_system/app/simpleos/feature/simple_app_startup_spec.spl` | `doc/06_spec/test/03_system/app/simpleos/feature/simple_app_startup_spec.md` | Full |
| REQ-102 | SimpleOS launcher icon prefetch | `test/03_system/app/simpleos/feature/simple_app_startup_spec.spl` | `doc/06_spec/test/03_system/app/simpleos/feature/simple_app_startup_spec.md` | Full |
| NFR-STARTUP-001 | `simple run` arg parsing and mmap performance stay responsive | `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` | `doc/06_spec/test/02_integration/app/startup_argparse_mmap_perf_spec.md` | Full |
