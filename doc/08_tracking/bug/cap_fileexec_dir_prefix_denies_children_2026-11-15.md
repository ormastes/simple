# FileExec/FileRead directory prefix ("/sys/apps/") denied every child path

- **Status:** fixed (2026-11-15)
- **Where:** `src/os/kernel/types/capability_types.spl` `_path_prefix_allows`
- **Reproducer:** `test/01_unit/os/kernel/loader/managed_workload_launch_spec.spl`,
  `test/01_unit/os/services/container/container_runtime_spec.spl` (launch path
  returned -13 from `exec_cap_check_caps`). Direct probe: held
  `FileExec("/sys/apps/")` vs required `FileExec("/sys/apps/live-worker")` -> `false`.

## Root cause
After the prefix match, the boundary check required `required_path[len(prefix)] == '/'`.
For a prefix that already ends in `/` the next character is the first byte of the
child name, so every child of a directory-style prefix (all recipe prefixes such as
`/sys/apps/`, `/bin/`) was denied. `spawn_recipe_seed_parent_caps` therefore could
never authorize its own recipe.

## Fix
Return true when `held_prefix` ends with `/`; boundary check uses the char literal `'/'`.

## Verification
- probe: allows=true, `exec_cap_check_caps(seed caps, "/sys/apps/live-worker") == 0`
- `test/01_unit/os/kernel/security/executable_read_spec.spl` OK 5/5
- `test/01_unit/os/kernel/types/capability_types_spec.spl` 44/45, unchanged from HEAD
  (pre-existing "returns false for empty set" failure)

The launch specs stay RED on a separate defect:
`executable_authority_registry_slots_lost_on_store_2026-11-15.md`.
