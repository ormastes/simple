# Disk Launch Manifest Specification

> <details>

<!-- sdn-diagram:id=disk_launch_manifest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=disk_launch_manifest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

disk_launch_manifest_spec -> std
disk_launch_manifest_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=disk_launch_manifest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Disk Launch Manifest Specification

## Scenarios

### Disk launch manifest for resident-manifest launch

#### maps browser demo from the FreeBSD-style runtime path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(disk_manifest_filename_for_path("/usr/local/bin/browser-demo")).to_equal("BROWSER.APP")
```

</details>

#### maps browser demo to the packaged FAT32 manifest name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(disk_manifest_filename_for_path("/sys/apps/browser_demo")).to_equal("BROWSER.APP")
```

</details>

#### maps browser demo SMF package to the packaged FAT32 manifest name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(disk_manifest_filename_for_path("/sys/apps/browser_demo.smf")).to_equal("BROWSER.APP")
```

</details>

#### maps hello world from the FreeBSD-style runtime path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(disk_manifest_filename_for_path("/usr/bin/hello-world")).to_equal("HELLO.APP")
```

</details>

#### maps hello world to the packaged FAT32 manifest name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(disk_manifest_filename_for_path("/sys/apps/hello_world")).to_equal("HELLO.APP")
```

</details>

#### maps file manager from the FreeBSD-style runtime path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(disk_manifest_filename_for_path("/usr/bin/file-manager")).to_equal("FILEMAN.APP")
```

</details>

#### maps file manager to the packaged FAT32 manifest name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(disk_manifest_filename_for_path("/sys/apps/file_manager")).to_equal("FILEMAN.APP")
```

</details>

#### maps shell from the FreeBSD-style runtime path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(disk_manifest_filename_for_path("/bin/shell")).to_equal("SHELL.APP")
```

</details>

#### maps shell to the packaged FAT32 manifest name

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(disk_manifest_filename_for_path("/sys/apps/shell")).to_equal("SHELL.APP")
```

</details>

#### maps smux from the runtime and sys-app paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(disk_manifest_filename_for_path("/usr/bin/smux")).to_equal("SMUX.APP")
expect(disk_manifest_filename_for_path("/sys/apps/smux")).to_equal("SMUX.APP")
expect(disk_manifest_filename_for_path("/sys/apps/smux.smf")).to_equal("SMUX.APP")
```

</details>

#### maps AI CLI app paths to their staged manifest names

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(disk_manifest_filename_for_path("/usr/bin/codex")).to_equal("CODEX.APP")
expect(disk_manifest_filename_for_path("/sys/apps/codex")).to_equal("CODEX.APP")
expect(disk_manifest_filename_for_path("/sys/apps/claude.smf")).to_equal("CLAUDE.APP")
expect(disk_manifest_filename_for_path("/usr/bin/gemini")).to_equal("GEMINI.APP")
```

</details>

#### returns empty for unknown paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(disk_manifest_filename_for_path("/sys/apps/missing")).to_equal("")
```

</details>

#### parses the resident entry symbol from the manifest body

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "kind=resident_remote_app\nentry=browser_demo_remote_main\napp_id=/sys/apps/browser_demo\n"
expect(parse_disk_launch_entry_name(content)).to_equal("browser_demo_remote_main")
```

</details>

#### ignores comments and blank lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# comment\n\nentry=browser_demo_remote_main\n"
expect(parse_disk_launch_entry_name(content)).to_equal("browser_demo_remote_main")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/disk_launch_manifest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Disk launch manifest for resident-manifest launch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
