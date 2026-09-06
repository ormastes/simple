# SimpleOS kernel closure imports a stdlib contract module that does not exist

Date: 2026-08-31
Scope: goal item 2 — SimpleOS window-manager smoke tests with Vulkan-backed
evidence on x86_64 / aarch64 / riscv64. This blocks **all three** rows, not one.

## Verdict

`origin/main` (79126c25822) cannot build any SimpleOS kernel whose module
closure reaches `src/os/kernel/`. Three tracked `src/os/` files import

    std.common.contracts.os.server_data_namespace_v1

and that module is **not in the tree**. `src/lib/common/contracts/os/` contains
exactly one file, `dbfs_vfs_mount_capability_v1.spl`. Verified against committed
content, not a working copy:

```
$ git ls-tree -r --name-only origin/main | grep 'src/lib/common/contracts/os/'
src/lib/common/contracts/os/dbfs_vfs_mount_capability_v1.spl
```

## Importers (all present at origin/main)

| file | line |
|---|---|
| `src/os/apps/dbd/dbd_dbfs_adapter.spl` | 11 |
| `src/os/kernel/loader/dbd_launch_grants_v1.spl` | 18 |
| `src/os/kernel/scheduler/server_data_namespace_owner.spl` | 10 |

## Observed failure

Building the WM desktop kernel with the recipe used by
`check-simpleos-x86-64-wm-hello-lifecycle-evidence.shs` (native-build,
`--target x86_64-unknown-none`, entry
`examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`):

```
Module resolution error: Semantic("stdlib import
`std.common.contracts.os.server_data_namespace_v1` resolves from the project
stdlib roots only")
```

The diagnostic is misleading — it reads as a *root selection* problem, as if the
import merely needed a different `--source`/`SIMPLE_LIB`. It is not: the module
has no definition anywhere in the repository, so no root can satisfy it. A
clearer message ("no such stdlib module") would have cost this investigation
less time; that wording is itself worth fixing.

## Why no gate caught it

The kernel ELF the WM pixel-evidence gate needs
(`build/os/simpleos_x86_64_desktop_engine2d.elf`) has **no producer in the
tree** — `check-simpleos-x86-64-wm-host-vulkan-pixel-evidence.shs` is the only
file that names that path, and it consumes it as a precondition. So the gate
ERRORs at preconditions ("WM kernel ELF missing") long before anything tries to
compile the kernel, and the missing import never surfaces. The pre-push guards
do not close this either: `check-seed-builds-push.shs` compiles the **Rust
seed**, and `check-c-runtime-compiles-push.shs` runs `-fsyntax-only` over the
**C runtime**. Nothing on the push path compiles Simple `src/os/` sources.

## Impact

- x86_64 WM row: blocked. Kernel will not build.
- aarch64 / riscv64 WM rows: blocked for the same reason — the missing module is
  in the shared `src/os/kernel/` closure, not an arch port.

## Fix directions (not attempted here)

Either restore/author `src/lib/common/contracts/os/server_data_namespace_v1.spl`
exporting the symbols the three importers name, or drop the imports if the
contract was intentionally retired. Determine which from the design docs that
already reference this contract:
`doc/05_design/os/storage/server_data_namespace_owner_core_v1.md`,
`doc/05_design/os/storage/server_data_namespace_syscall_gate_v1.md`,
`doc/08_tracking/feature/simpleos_server_data_namespace_redemption_v1.md`.
`test/01_unit/os/services/vfs/server_data_namespace_owner_spec.spl` exercises the
owner and will pin whichever direction is chosen.

Follow-up worth doing in the same change: give the WM desktop kernel a real
build script (there is an arm64 precedent,
`scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs`) so that a
broken `src/os/` closure fails loudly instead of hiding behind a
missing-artifact precondition ERROR.
