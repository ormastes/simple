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

Runnable source: 34 lines folded for reproduction.
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

#### models requested SimpleOS host configurations

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val configs = simpleos_host_configs()
val serial = simpleos_host_config("fpga-serial").unwrap()
val qemu = simpleos_host_config("qemu-network-gui").unwrap()
val fpga_network = simpleos_host_config("fpga-network").unwrap()
expect(configs.len()).to_equal(3)
expect(serial.arch).to_equal("riscv64")
expect(serial.serial_console).to_equal(true)
expect(serial.network_services.len()).to_equal(0)
expect(serial.optimization_profile).to_equal("simpleos-host-aggressive")
expect(serial.filesystem_binary_paths).to_equal(["/usr/bin/simple", "/usr/bin/simple.smf", "/SYS/APPS/SIMPLSTC.SMF"])
expect(serial.check_commands[0]).to_equal("sh scripts/fpga/check_kv260_telnet_serial_system.shs")
expect(qemu.network_services).to_equal(["ssh", "web", "db"])
expect(qemu.gui_backend).to_equal("vulkan")
expect(qemu.wm_modes).to_equal(["full"])
expect(qemu.binary_launch).to_equal("base-filesystem")
expect(qemu.optimization_profile).to_equal("simpleos-host-aggressive")
expect(qemu.check_commands).to_contain("bin/simple-interp os test-scenario rv64-ssh")
expect(qemu.check_commands).to_contain("sh scripts/qemu/qemu_rv64_http_test.shs --expect-http-only --with-display --with-storage")
expect(qemu.check_commands).to_contain("sh scripts/qemu/check_simpleos_rv64_db_server.shs --artifacts <dir>")
expect(qemu.check_commands).to_contain("SIMPLEOS_DESKTOP_QMP_TARGET=wm-simple-web bin/simple-interp run src/app/test/simpleos_desktop_qmp_launch.spl")
expect(fpga_network.machine).to_equal("fpga")
expect(fpga_network.network_services).to_equal(["ssh", "web", "db"])
expect(fpga_network.filesystem_binary_paths).to_equal(["/usr/bin/simple", "/usr/bin/simple.smf", "/SYS/APPS/SIMPLSTC.SMF"])
expect(fpga_network.check_commands[0]).to_equal("sh scripts/fpga/check_kv260_simple_rv64_network.shs --artifacts <dir>")
expect(wm_modes_for_host("simpleos")).to_equal(["full"])
expect(wm_modes_for_host("linux")).to_equal(["full", "window"])
expect(wm_mode_allowed_for_host("simpleos", "full")).to_equal(true)
expect(wm_mode_allowed_for_host("simpleos", "window")).to_equal(false)
expect(wm_mode_allowed_for_host("macos", "window")).to_equal(true)
expect(wm_mode_validation_error("simpleos", "window")).to_equal("wm mode 'window' is not available on host 'simpleos'")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/simple_os_primary_spec.spl` |
| Updated | 2026-06-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS primary surfaces

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
