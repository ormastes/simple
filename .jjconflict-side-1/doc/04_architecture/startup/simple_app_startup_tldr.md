# Simple App Startup Architecture — TLDR

Simple startup is metadata-driven for native binaries, scripts, SMF files, and
SimpleOS launcher apps. Startup reads `LaunchMetadata` first, then decides
whether to include argv parsing, mmap/cache warmup, and native/SMF dynlib
loading.

## Core Shape

- One metadata contract covers `native | script | smf`: target OS/arch/ABI, arg
  parser policy, mmap/cache hint, native dynlibs, and SMF dynlibs.
- Native builds append an embedded `SIMPLE_LAUNCH_V1` metadata trailer; sidecar
  metadata is auxiliary for explicit checks.
- Scripts use generated module-graph metadata; SMF files carry metadata in the
  embedded `.launch_meta` SMF section.
- SimpleOS paths use `launch_metadata_for_simpleos_path(...)` and
  `simple launch-meta check --simpleos /sys/apps/app.smf`.
- SimpleOS WM hover prefetch checks `app_registry_cached_bytes(...)`, asks
  `g_vfs_read_executable_bytes(...)` to warm misses, and must not launch, call
  dynlibs, or map process-callable code.

## Operational Notes

- startup: `src/app/startup/launch_metadata.spl` computes the include/load/cache
  startup plan.
- file args: `src/app/io/cli_commands_part1.spl` normalizes script `argv[0]`
  once before driver dispatch.
- cache/index: host mmap uses mmap/prefetch; SimpleOS uses app-registry/VFS
  cache/read-ahead.
- invalidation: script metadata must be keyed by module graph hashes, target,
  and compiler version.
- perf/RSS: arg parser, mmap/cache, and dynlib loader code should be excluded or
  capability-gated when metadata says unused.
- verification: run
  `test/02_integration/app/startup_argparse_mmap_perf_spec.spl` for `simple run`
  startup changes.

## Open Next

- [full architecture](simple_app_startup.md)
- [test plan](../../03_plan/sys_test/simple_app_startup.md)
- [implementation plan](../../03_plan/app/misc/simple_app_startup.md)
- [startup policy](../../../src/app/startup/launch_metadata.spl)
- [SimpleOS launcher](../../../src/os/services/launcher/launcher.spl)
