# Ssh Session Shell Specification

> <details>

<!-- sdn-diagram:id=ssh_session_shell_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ssh_session_shell_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ssh_session_shell_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ssh_session_shell_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Session Shell Specification

## Scenarios

### SSH shell session bridge

#### emits the shell banner and prompt when the session shell starts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = ssh_shell_boot_output_for_test()
expect(output).to_contain("SimpleOS Shell v0.2")
expect(output).to_contain("Type 'help' for available commands.")
expect(output).to_contain("user@simpleos")
expect(output).to_contain("$ ")
```

</details>

#### round-trips a built-in command through the shell transport adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = ssh_shell_roundtrip_output_for_test("echo ssh\n")
expect(output).to_contain("ssh")
expect(output).to_end_with("$ ")
```

</details>

#### keeps multi-command input ordered across one transport chunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = ssh_shell_roundtrip_output_for_test("echo hi\necho bye\n")
expect(output).to_contain("hi")
expect(output).to_contain("bye")
expect(output).to_end_with("$ ")
```

</details>

#### resolves SSH shell SMF commands through the filesystem app registry

-  seed launchable apps
   - Expected: report.command equals `simple.smf`
   - Expected: report.resolved_path equals `/usr/bin/simple.smf`
   - Expected: report.fat32_alias equals `/SYS/APPS/SIMPLSTC.SMF`
   - Expected: report.root_alias equals `/SIMPLSTC.SMF`
   - Expected: report.launchable is true
   - Expected: report.smf_backed is true
   - Expected: report.shell_exec_path is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seed_launchable_apps()
val report = ssh_shell_launch_report_for_test("simple.smf --version")
expect(report.command).to_equal("simple.smf")
expect(report.resolved_path).to_equal("/usr/bin/simple.smf")
expect(report.fat32_alias).to_equal("/SYS/APPS/SIMPLSTC.SMF")
expect(report.root_alias).to_equal("/SIMPLSTC.SMF")
expect(report.launchable).to_equal(true)
expect(report.smf_backed).to_equal(true)
expect(report.shell_exec_path).to_equal(true)
```

</details>

#### resolves SSH shell executable-file commands through the same launch path

-  seed launchable apps
   - Expected: report.command equals `simple`
   - Expected: report.resolved_path equals `/usr/bin/simple`
   - Expected: report.fat32_alias equals `/SYS/APPS/SIMPLSTC.SMF`
   - Expected: report.root_alias equals `/SIMPLSTC.SMF`
   - Expected: report.launchable is true
   - Expected: report.smf_backed is true
   - Expected: report.shell_exec_path is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seed_launchable_apps()
val report = ssh_shell_launch_report_for_test("simple --check")
expect(report.command).to_equal("simple")
expect(report.resolved_path).to_equal("/usr/bin/simple")
expect(report.fat32_alias).to_equal("/SYS/APPS/SIMPLSTC.SMF")
expect(report.root_alias).to_equal("/SIMPLSTC.SMF")
expect(report.launchable).to_equal(true)
expect(report.smf_backed).to_equal(true)
expect(report.shell_exec_path).to_equal(true)
```

</details>

#### resolves SSH shell sh commands to the shell SMF executable

-  seed launchable apps
   - Expected: report.command equals `sh`
   - Expected: report.resolved_path equals `/usr/bin/sh`
   - Expected: report.fat32_alias equals `/SYS/APPS/SHELLSMF.SMF`
   - Expected: report.root_alias equals `/SHELLSMF.SMF`
   - Expected: report.launchable is true
   - Expected: report.smf_backed is true
   - Expected: report.shell_exec_path is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_seed_launchable_apps()
val report = ssh_shell_launch_report_for_test("sh -lc pwd")
expect(report.command).to_equal("sh")
expect(report.resolved_path).to_equal("/usr/bin/sh")
expect(report.fat32_alias).to_equal("/SYS/APPS/SHELLSMF.SMF")
expect(report.root_alias).to_equal("/SHELLSMF.SMF")
expect(report.launchable).to_equal(true)
expect(report.smf_backed).to_equal(true)
expect(report.shell_exec_path).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/ssh_session_shell_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SSH shell session bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
