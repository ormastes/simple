# SimpleOS primary Linux-like tool filesystem-launch inventory

Static source inventory, updated 2026-08-26. This is not a build, boot, or
runtime result. `implemented` means a source entry point exists; `cataloged`
means a source-level identity/plan exists; `launcher-wired` means the generic
launcher explicitly recognizes and rejects the path until it has loader
authority. None of those terms means that filesystem bytes exist or that a
guest launched them.

| Tool set | Implemented source evidence | Catalog / path evidence | Generic launcher wiring | x86_64, aarch64, riscv64 filesystem launch |
|---|---|---|---|---|
| SimpleBox core: `echo true false pwd seq cat head wc` | `src/os/tools/simplebox/simplebox_main.spl` routes exactly these eight names; its dispatcher implements `echo`, `true`, `false`, and `pwd`, with `seq`, `cat`, `head`, and `wc` routed by the entry point. | `simplebox_artifact_contract.spl` declares canonical `/bin/simplebox` and these eight applets. It is a contract, not installed bytes. | `primary_tool_artifact_gate.spl` blocks `/bin/simplebox`, `echo`, `pwd`, `seq`, `cat`, `head`, and `wc` through `launcher_launch_path_with_args` (exit 126). It does **not** include `/bin/true` or `/bin/false`; those aliases are therefore not proven generic-launcher-wired. | **Blocked / no static launch proof** on all three. No target payload digest, signed admission record, loader token, or FAT32/DBFS/NVFS receipt was found. |
| Dedicated checksum tools: `sha256sum md5sum` | `src/os/apps/coreutils/checksum.spl` exports `main_sha256sum` and `main_md5sum`; the artifact contract supplies `/usr/bin/...` identities. | Catalog rows name separate payload paths. Package identities deliberately have empty digest/receipt fields. | Both canonical paths are recognized by the generic authority gate and reject before spawn. | **Blocked / no static launch proof** on all three. |
| Dedicated text/process tools: `grep ps` | `src/os/apps/coreutils/grep.spl` exports `main_grep`; `ps.spl` exports `main_ps`; artifact contracts supply `/usr/bin/grep` and `/usr/bin/ps`. | Catalog rows name separate payload paths. No payload bytes or admitted record is present. | Both canonical paths are recognized by the generic authority gate and reject before spawn. | **Blocked / no static launch proof** on all three. |
| Additional SimpleBox inventory names (for example `printf`, `tail`, `tee`, `cp`, `ls`, `find`, `sort`, `sed`, `join`) | `simplebox_inventory_v1.spl` lists 41 names, but the concrete dispatcher/main above does not route them. | `primary_linux_tool_catalog_bundle_v1.spl` claims a 45-command / five-payload plan, but imports `SIMPLEBOX_APPLET_COUNT_V1`, `simplebox_applet_names_v1`, and `simplebox_canonical_aliases_v1`; no definitions of those symbols exist in the current `src/os/tools/simplebox` tree. | No verified route from those inventory names to the concrete dispatcher or an installed artifact. | **Not launchable by static evidence**; treat as inventory/planning only, not implemented filesystem commands. |

## Architecture interpretation

`executable_target_dispatch_v1.spl` marks process-image mapping policy ready
for `x86_64`, `aarch64`, and `riscv64`. That is only architecture-routing
readiness. It supplies neither a file handle nor executable bytes or
authority, so it does not upgrade any table row to filesystem-launchable.

The current generic gate is deliberately fail-closed for the paths it covers:
`launcher_registry.spl` returns `-126` before process spawn whenever
`primary_tool_path_requires_loader_authority_v1` matches. A rejection is
evidence of a guard, not a successful launch. Conversely, the absent
`/bin/true` and `/bin/false` checks are a wiring gap, not evidence that either
alias can launch.

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
