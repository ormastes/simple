# Ssh Session Shell Specification

> Tests covering SSH shell session bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Session Shell Specification

## Scenarios

### SSH shell session bridge

#### emits the shell banner and prompt when the session shell starts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits the shell banner and prompt when the session shell starts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits the shell banner and prompt when the session shell starts")
val output = ssh_shell_boot_output_for_test()
expect(output).to_contain("SimpleOS Shell v0.2")
expect(output).to_contain("Type 'help' for available commands.")
expect(output).to_contain("user@simpleos")
expect(output).to_contain("$ ")
```

</details>

#### round-trips a built-in command through the shell transport adapter

- round-trips a built-in command through the shell transport adapter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a built-in command through the shell transport adapter")
val output = ssh_shell_roundtrip_output_for_test("echo ssh\n")
expect(output).to_contain("ssh")
expect(output).to_end_with("$ ")
```

</details>

#### keeps multi-command input ordered across one transport chunk

- keeps multi-command input ordered across one transport chunk


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps multi-command input ordered across one transport chunk")
val output = ssh_shell_roundtrip_output_for_test("echo hi\necho bye\n")
expect(output).to_contain("hi")
expect(output).to_contain("bye")
expect(output).to_end_with("$ ")
```

</details>

#### executes the command and returns its output, not just a prompt

- executes the command and returns its output, not just a prompt


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("executes the command and returns its output, not just a prompt")
# Absolute oracle: a command sent through the shell bridge must produce
# the command's own output. Before the fix the bridge returned banner +
# prompt only, because `for ch in input` char values never compared
# equal to '\n' so no line was ever executed.
val output = ssh_shell_roundtrip_output_for_test("echo sshdfix-marker\n")
expect(output).to_contain("sshdfix-marker")
expect(output).to_contain("SimpleOS Shell v0.2")
```

</details>

#### emits exactly banner, command output and prompt for one command

- emits exactly banner, command output and prompt for one command
   - Expected: output equals `SimpleOS Shell v0.2\nType 'help' for available commands.\n\nuser@simpleos:/# ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits exactly banner, command output and prompt for one command")
# Absolute oracle: full byte-for-byte transcript, so a bridge that
# returned banner + prompt only (the reported defect) cannot pass by
# coincidence, and neither can one that drops or duplicates output.
val output = ssh_shell_roundtrip_output_for_test("echo abc\n")
expect(output).to_equal("SimpleOS Shell v0.2\nType 'help' for available commands.\n\nuser@simpleos:/# $ \nabc\nuser@simpleos:/# $ ")
```

</details>

#### emits exactly the two command outputs in order for two commands

- emits exactly the two command outputs in order for two commands
   - Expected: output equals `SimpleOS Shell v0.2\nType 'help' for available commands.\n\nuser@simpleos:/# ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits exactly the two command outputs in order for two commands")
val output = ssh_shell_roundtrip_output_for_test("whoami\npwd\n")
expect(output).to_equal("SimpleOS Shell v0.2\nType 'help' for available commands.\n\nuser@simpleos:/# $ \nroot\nuser@simpleos:/# $ \n/\nuser@simpleos:/# $ ")
```

</details>

#### returns whoami output through the shell bridge

- returns whoami output through the shell bridge


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns whoami output through the shell bridge")
val output = ssh_shell_roundtrip_output_for_test("whoami\n")
expect(output).to_contain("root")
```

</details>

#### returns pwd output through the shell bridge

- returns pwd output through the shell bridge


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns pwd output through the shell bridge")
val output = ssh_shell_roundtrip_output_for_test("pwd\n")
expect(output).to_contain("/")
```

</details>

#### reports unknown commands instead of silently swallowing them

- reports unknown commands instead of silently swallowing them


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports unknown commands instead of silently swallowing them")
val output = ssh_shell_roundtrip_output_for_test("no_such_cmd_xyz\n")
expect(output).to_contain("command not found: no_such_cmd_xyz")
```

</details>

#### terminates a line on CRLF as well as bare LF

- terminates a line on CRLF as well as bare LF


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("terminates a line on CRLF as well as bare LF")
val output = ssh_shell_roundtrip_output_for_test("echo crlf-marker\r\n")
expect(output).to_contain("crlf-marker")
```

</details>

#### does not execute an unterminated line

- does not execute an unterminated line
   - Expected: output does not contain `pending-marker`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not execute an unterminated line")
# No trailing newline: the command must stay buffered, not run.
val output = ssh_shell_roundtrip_output_for_test("echo pending-marker")
expect(output.contains("pending-marker")).to_equal(false)
```

</details>

#### resolves SSH shell SMF commands through the filesystem app registry

- resolves SSH shell SMF commands through the filesystem app registry
   - Expected: report.command equals `simple.smf`
   - Expected: report.resolved_path equals `/usr/bin/simple.smf`
   - Expected: report.fat32_alias equals `/SYS/APPS/SIMPLSTC.SMF`
   - Expected: report.root_alias equals `/SIMPLSTC.SMF`
   - Expected: report.launchable is true
   - Expected: report.smf_backed is true
   - Expected: report.shell_exec_path is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves SSH shell SMF commands through the filesystem app registry")
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

- resolves SSH shell executable-file commands through the same launch path
   - Expected: report.command equals `simple`
   - Expected: report.resolved_path equals `/usr/bin/simple`
   - Expected: report.fat32_alias equals `/SYS/APPS/SIMPLSTC.SMF`
   - Expected: report.root_alias equals `/SIMPLSTC.SMF`
   - Expected: report.launchable is true
   - Expected: report.smf_backed is true
   - Expected: report.shell_exec_path is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves SSH shell executable-file commands through the same launch path")
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

- resolves SSH shell sh commands to the shell SMF executable
   - Expected: report.command equals `sh`
   - Expected: report.resolved_path equals `/usr/bin/sh`
   - Expected: report.fat32_alias equals `/SYS/APPS/SHELLSMF.SMF`
   - Expected: report.root_alias equals `/SHELLSMF.SMF`
   - Expected: report.launchable is true
   - Expected: report.smf_backed is true
   - Expected: report.shell_exec_path is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves SSH shell sh commands to the shell SMF executable")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSH shell session bridge.
- SSH shell session bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `705126cf650635f882f63036aa83728d7eded73c748fc95f663cdcb8c95421dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `705126cf650635f882f63036aa83728d7eded73c748fc95f663cdcb8c95421dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `705126cf650635f882f63036aa83728d7eded73c748fc95f663cdcb8c95421dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/sshd/ssh_session_shell_spec.spl
mirror: doc/06_spec/01_unit/os/apps/sshd/ssh_session_shell_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/sshd/ssh_session_shell_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/sshd/ssh_session_shell_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/sshd/ssh_session_shell_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits the shell banner and prompt when the session shell starts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/ssh_session_shell_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a built-in command through the shell transport adapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/ssh_session_shell_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps multi-command input ordered across one transport chunk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
