# Simpleos Cli App Catalog Specification

> 1. dir create all

<!-- sdn-diagram:id=simpleos_cli_app_catalog_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_cli_app_catalog_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_cli_app_catalog_spec -> std
simpleos_cli_app_catalog_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_cli_app_catalog_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Cli App Catalog Specification

## Scenarios

### SimpleOS CLI app catalog disk staging

#### stages the full src/app catalog into the desktop FAT32 image

1. dir create all
   - Expected: ok is false
2. "src count=$
3. "disk catalog=$
4. "disk count=$
   - Expected: result.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all("build/os")
val ok = ensure_desktop_disk_image()
if not ok:
    print "[simpleos_cli_app_catalog_spec] disk image unavailable, skipping"
    expect(ok).to_equal(false)
else:
    val img_path = desktop_disk_image_path()
    val cmd =
        "src_count=$(grep -Ev '^(#|$)' scripts/simpleos_cli_app_catalog.txt | wc -l | tr -d ' ');" +
        "if command -v mtype >/dev/null 2>&1; then " +
        "mtype -i '" + img_path + "' ::/SYS/APPS/SHELL.APP 2>/dev/null | grep -q 'shell_remote_main' || exit 1; " +
        "mtype -i '" + img_path + "' ::/SYS/APPS/SMUX.APP 2>/dev/null | grep -q 'smux_remote_main' || exit 1; " +
        "disk_catalog=$(mtype -i '" + img_path + "' ::/SYS/APPS/SIMPLECLI.CAT 2>/dev/null) || exit 1; " +
        "printf '%s\n' \"$disk_catalog\" | grep -q '^info|src/app/info/main.spl|smoke|staged$' || exit 1; " +
        "printf '%s\n' \"$disk_catalog\" | grep -q '^list|src/app/list/main.spl|smoke|staged$' || exit 1; " +
        "printf '%s\n' \"$disk_catalog\" | grep -q '^stats|src/app/stats/main.spl|smoke|staged$' || exit 1; " +
        "mdir -i '" + img_path + "' ::/SYS/APPS/simple_browser >/dev/null 2>&1 || exit 1; " +
        "mdir -i '" + img_path + "' ::/SYS/APPS/simple_browser.smf >/dev/null 2>&1 || exit 1; " +
        "mdir -i '" + img_path + "' ::/SYS/APPS/smux >/dev/null 2>&1 || exit 1; " +
        "mdir -i '" + img_path + "' ::/SYS/APPS/smux.smf >/dev/null 2>&1 || exit 1; " +
        "mdir -i '" + img_path + "' ::/usr/bin/smux >/dev/null 2>&1 || exit 1; " +
        "mdir -i '" + img_path + "' ::/SYS/APPS/simple_compiler_gui >/dev/null 2>&1 || exit 1; " +
        "mdir -i '" + img_path + "' ::/SYS/APPS/simple_interpreter_gui >/dev/null 2>&1 || exit 1; " +
        "mdir -i '" + img_path + "' ::/SYS/APPS/simple_loader_gui >/dev/null 2>&1 || exit 1; " +
        "mdir -i '" + img_path + "' ::/SYS/APPS/llvm_gui >/dev/null 2>&1 || exit 1; " +
        "mdir -i '" + img_path + "' ::/SYS/APPS/rust_gui >/dev/null 2>&1 || exit 1; " +
        "disk_count=$(printf '%s\n' \"$disk_catalog\" | grep -Ev '^(#|$)' | wc -l | tr -d ' '); " +
        "[ \"$src_count\" = \"$disk_count\" ]; " +
        "else " +
        "grep -a -q 'shell_remote_main' '" + img_path + "' && " +
        "grep -a -q 'smux_remote_main' '" + img_path + "' && " +
        "grep -a -q 'SMUX.APP' '" + img_path + "' && " +
        "grep -a -q 'info|src/app/info/main.spl|smoke|staged' '" + img_path + "' && " +
        "grep -a -q 'list|src/app/list/main.spl|smoke|staged' '" + img_path + "' && " +
        "grep -a -q 'stats|src/app/stats/main.spl|smoke|staged' '" + img_path + "' && " +
        "grep -a -q '/sys/apps/simple_browser' '" + img_path + "' && " +
        "grep -a -q '/sys/apps/smux' '" + img_path + "' && " +
        "grep -a -q 'simple_compiler_gui' '" + img_path + "' && " +
        "grep -a -q 'simple_interpreter_gui' '" + img_path + "' && " +
        "grep -a -q 'simple_loader_gui' '" + img_path + "' && " +
        "grep -a -q 'llvm_gui' '" + img_path + "' && " +
        "grep -a -q 'rust_gui' '" + img_path + "'; " +
        "fi"
    val result = run_shell(cmd)
    if result.2 != 0:
        print result.0
        print result.1
    expect(result.2).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_cli_app_catalog_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS CLI app catalog disk staging

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
