# Managed workload launch specs hardcode an x86_64 image; adoption rejects it on arm64 hosts

- **Status:** open (2026-11-15)
- **Where:** `src/os/kernel/scheduler/scheduler_executable_adoption.spl:207`
  (`_authenticated_consumer_arch_matches_v1(consumer, get_arch())`), with specs
  `test/01_unit/os/kernel/loader/managed_workload_launch_spec.spl` (3/5),
  `test/01_unit/os/services/container/container_runtime_spec.spl` (4/5),
  `runtime_provider_v1_spec.spl` (2/3), `macos_simpleos_guest_dispatch_v1_spec.spl` (2/3)
- **Host:** macOS arm64, rebuilt seed with the registry fix

## Evidence
On this host, `get_arch()` is `@cfg(arm64)` -> `Architecture.Arm64`. The specs
build `_minimal_x86_64_elf()` and pass `Architecture.X86_64`. Adoption returns
`RollbackUnavailable`. The cleanup release then returns `CloseFailed`, and the
caller sees `pid=-13`. On an x86_64 host the same path would reach publication.

## Unblock
Choose one: (a) the specs build a minimal ELF for `get_arch()`; or (b) the owner
approves an arch tag (only `# @platform:` OS tags exist). Do not skip these specs
without approval. Separately, the cleanup `CloseFailed` after an arch rejection
should be checked; a rejected adoption should release cleanly.
