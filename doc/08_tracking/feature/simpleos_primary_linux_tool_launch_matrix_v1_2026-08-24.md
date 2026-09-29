# SimpleOS primary Linux-like tool filesystem-launch inventory

Static source inventory, updated 2026-08-26. This is not a build, boot, or
runtime result. `implemented` means a source entry point exists; `cataloged`
means a source-level identity/plan exists; `launcher-wired` means the generic
launcher explicitly recognizes and rejects the path until it has loader
authority. None of those terms means that filesystem bytes exist or that a
guest launched them.

| Tool set | Implemented source evidence | Catalog / path evidence | Generic launcher wiring | x86_64, aarch64, riscv64 filesystem launch |
|---|---|---|---|---|
| SimpleBox core: `echo true false pwd seq cat head wc` | `src/os/tools/simplebox/simplebox_main.spl` routes exactly these eight names; its dispatcher implements `echo`, `true`, `false`, and `pwd`, with `seq`, `cat`, `head`, and `wc` routed by the entry point. | `simplebox_inventory_v1.spl` is the closed eight-name source; `simplebox_artifact_contract.spl` declares canonical `/bin/simplebox` and its eight exact aliases. It is a contract, not installed bytes. | `primary_tool_artifact_gate.spl` reaches `simplebox_path_requires_loader_authority_v1`, which blocks the canonical path and every one of the eight declared aliases through `launcher_launch_path_with_args` (exit 126). | **Blocked / no static launch proof** on all three. No target payload digest, signed admission record, loader token, or FAT32/DBFS/NVFS receipt was found. |
| Dedicated checksum tools: `sha256sum md5sum` | `src/os/apps/coreutils/checksum.spl` exports `main_sha256sum` and `main_md5sum`; the artifact contract supplies `/usr/bin/...` identities. | Catalog rows name separate payload paths. Package identities deliberately have empty digest/receipt fields. | Both canonical paths are recognized by the generic authority gate and reject before spawn. | **Blocked / no static launch proof** on all three. |
| Dedicated text/process tools: `grep ps` | `src/os/apps/coreutils/grep.spl` exports `main_grep`; `ps.spl` exports `main_ps`; artifact contracts supply `/usr/bin/grep` and `/usr/bin/ps`. | Catalog rows name separate payload paths. No payload bytes or admitted record is present. | Both canonical paths are recognized by the generic authority gate and reject before spawn. | **Blocked / no static launch proof** on all three. |
| Other shell/helper command names (for example `printf`, `tail`, `tee`, `cp`, `ls`, `find`, `sort`, `sed`, `join`) | Some have separate implementations elsewhere, but `simplebox_inventory_v1.spl` excludes them because `simplebox_main.spl` does not route them. | `primary_linux_tool_catalog_bundle_v1.spl` defines a coherent 12-command / five-payload plan: eight routed SimpleBox aliases plus standalone `sha256sum`, `md5sum`, `grep`, and `ps`. | No SimpleBox alias or installed-payload claim is made for the excluded names. | **Not launchable through SimpleBox by static evidence**. |

## Architecture interpretation

`executable_target_dispatch_v1.spl` marks process-image mapping policy ready
for `x86_64`, `aarch64`, and `riscv64`. That is only architecture-routing
readiness. It supplies neither a file handle nor executable bytes or
authority, so it does not upgrade any table row to filesystem-launchable.

The current generic gate is deliberately fail-closed for the paths it covers:
`launcher_registry.spl` returns `-126` before process spawn whenever
`primary_tool_path_requires_loader_authority_v1` matches. A rejection is
evidence of a guard, not a successful launch. Conversely, the absent
All eight declared SimpleBox aliases are matched by the generic gate; rejection
is a guard result, not evidence that an alias can launch.

Promotion for every architecture needs target-native bytes at the exact path,
their digest and signed admission record, a guest-verified filesystem open,
a consumed loader-owned authority token, and an operation/error receipt for
the selected filesystem. None is established here.

### Evidence locations

- `src/os/tools/simplebox/simplebox_main.spl`
- `src/os/tools/simplebox/simplebox_dispatch.spl`
- `src/os/tools/simplebox/simplebox_artifact_contract.spl`
- `src/os/tools/simplebox/simplebox_inventory_v1.spl`
- `src/os/kernel/loader/primary_linux_tool_catalog_bundle_v1.spl`
- `src/os/kernel/loader/executable_target_dispatch_v1.spl`
- `src/os/services/launcher/primary_tool_artifact_gate.spl`
- `src/os/services/launcher/launcher_registry.spl`
