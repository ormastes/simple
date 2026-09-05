# Simple Os Primary Specification

> <details>

<!-- sdn-diagram:id=simple_os_primary_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_os_primary_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_os_primary_spec -> std
simple_os_primary_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_os_primary_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Os Primary Specification

## Scenarios

### SimpleOS primary surfaces

#### covers GUI app names

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val apps = primary_apps()
expect(apps[2].name).to_equal("Markdown Editor")
expect(apps[3].name).to_equal("File Explorer")
expect(apps[5].name).to_equal("Drawer")
expect(apps[6].name).to_equal("Minesweeper")
expect(apps[7].name).to_equal("Browser")
expect(apps[8].name).to_equal("Image Viewer")
expect(apps[9].name).to_equal("PDF Viewer")
expect(apps[10].name).to_equal("Window Manager")
```

</details>

#### models markdown notes and drawer lookup

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val note = markdown_note("/home/notes/os.md", "# SimpleOS\nSee [[Kernel]].")
val filtered = drawer_query(drawer_state(), "settings")
expect(note.title).to_equal("SimpleOS")
expect(note.wiki_links[0]).to_equal("Kernel")
expect(drawer_visible(filtered)[0].name).to_equal("Settings")
expect(drawer_selected_path(filtered)).to_equal("/sys/apps/settings")
```

</details>

#### covers system and CLI essentials

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_system_config()
val commands = primary_cli_commands()
expect(config.service_manager).to_equal("OpenRC")
expect(config.bootloader).to_equal("Limine")
expect(config.standard_library).to_equal("musl")
expect(commands[1].name).to_equal("tmux")
expect(commands[2].name).to_equal("ssh")
expect(commands[4].name).to_equal("mkdir")
expect(commands[5].name).to_equal("chmod")
expect(commands[6].name).to_equal("sudo")
expect(commands[7].name).to_equal("pkg")
expect(commands[8].name).to_equal("git")
expect(commands[9].name).to_equal("rg")
expect(commands[10].name).to_equal("fd")
expect(commands[11].name).to_equal("btop")
expect(commands[12].name).to_equal("curl")
expect(commands[13].name).to_equal("man")
expect(commands[14].name).to_equal("gdb")
expect(commands[15].name).to_equal("xxd")
expect(commands[16].name).to_equal("picocom")
expect(commands[17].name).to_equal("zig")
```

</details>

#### plans packages and tmux windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = package_plan(["install", "git"]).unwrap()
val session = tmux_add_window(tmux_session("dev"), "ssh host")
expect(plan.package_name).to_equal("git")
expect(session.windows.len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/simple_os_primary_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS primary surfaces

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
