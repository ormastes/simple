# SOSIX positioned writes leave retained execute identity current

- **Observed:** 2026-09-28 on `origin/main` at `e4243e67153`
- **Status:** source fix and regression case prepared; source-matched verification pending

`MountTable.positioned_write_bytes` delegates to FAT32, NVFS or DBFS and returns
the written byte count without advancing the mount's `content_generation`.
`execute_binding_is_current` checks that generation. A retained executable
binding can therefore still appear current after its bytes change through the
positioned route, whereas `write` and `pwrite` advance the generation.

The fix rejects a wrong-driver request before dispatch, preflights generation
capacity, and conservatively advances the generation after any nonempty request
that reaches a supported driver. FAT32 can return an error after writing bytes
if cursor restoration fails; NVFS POSIX can fail after an inner write while
mirroring to NVMe. A focused regression checks that a wrong-driver rejection
leaves the binding current and a successful NVFS positioned write makes it stale.

The local pure-Simple binary at
`bin/release/aarch64-apple-darwin-macho/simple` exited 139 during discovery of
the focused spec, before executing assertions. The source-matched lib/core and
MCP smoke gates remain required before this can be marked verified.
