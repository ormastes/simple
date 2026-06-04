# Simple App Startup Architecture — TLDR

Simple startup is metadata-driven for native binaries, scripts, SMF files, and
SimpleOS launcher apps. Startup reads `LaunchMetadata` first, then decides
whether to include argv parsing, mmap/cache warmup, and native/SMF dynlib
loading.

## Core Shape

- One metadata contract covers `native | script | smf`: target OS/arch/ABI, arg
  parser policy, mmap/cache hint, native dynlibs, and SMF dynlibs.
- Native builds should embed metadata and emit a sidecar for
  `simple launch-meta check`.
- Scripts use generated module-graph metadata; SMF files carry metadata in the
  SMF manifest/header.
- SimpleOS paths use `launch_metadata_for_simpleos_path(...)` and
  `simple launch-meta check --simpleos /sys/apps/app.smf`.
- SimpleOS WM hover prefetch warms/checks executable bytes but must not launch,
  call dynlibs, or map process-callable code.

## Operational Notes

- startup: `src/app/startup/launch_metadata.spl` computes the include/load/cache
  startup plan.
- cache/index: host mmap uses mmap/prefetch; SimpleOS uses app-registry/VFS
  cache/read-ahead.
- invalidation: script metadata must be keyed by module graph hashes, target,
  and compiler version.
- perf/RSS: arg parser, mmap/cache, and dynlib loader code should be excluded or
  capability-gated when metadata says unused.

## Open Next

- [full architecture](simple_app_startup.md)
- [test plan](../03_plan/sys_test/simple_app_startup.md)
- [startup policy](../../src/app/startup/launch_metadata.spl)
- [SimpleOS launcher](../../src/os/services/launcher/launcher.spl)
