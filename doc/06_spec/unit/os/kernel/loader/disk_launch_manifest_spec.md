# Disk Launch Manifest Specification

> Tests covering Disk launch manifest for resident-manifest launch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Disk Launch Manifest Specification

## Scenarios

### Disk launch manifest for resident-manifest launch

#### maps browser demo from the FreeBSD-style runtime path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- maps browser demo from the FreeBSD-style runtime path
   - Expected: disk_manifest_filename_for_path("/usr/local/bin/browser-demo") equals `BROWSER.APP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps browser demo from the FreeBSD-style runtime path")
expect(disk_manifest_filename_for_path("/usr/local/bin/browser-demo")).to_equal("BROWSER.APP")
```

</details>

#### maps browser demo to the packaged FAT32 manifest name

- maps browser demo to the packaged FAT32 manifest name
   - Expected: disk_manifest_filename_for_path("/sys/apps/browser_demo") equals `BROWSER.APP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps browser demo to the packaged FAT32 manifest name")
expect(disk_manifest_filename_for_path("/sys/apps/browser_demo")).to_equal("BROWSER.APP")
```

</details>

#### maps browser demo SMF package to the packaged FAT32 manifest name

- maps browser demo SMF package to the packaged FAT32 manifest name
   - Expected: disk_manifest_filename_for_path("/sys/apps/browser_demo.smf") equals `BROWSER.APP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps browser demo SMF package to the packaged FAT32 manifest name")
expect(disk_manifest_filename_for_path("/sys/apps/browser_demo.smf")).to_equal("BROWSER.APP")
```

</details>

#### maps hello world from the FreeBSD-style runtime path

- maps hello world from the FreeBSD-style runtime path
   - Expected: disk_manifest_filename_for_path("/usr/bin/hello-world") equals `HELLO.APP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps hello world from the FreeBSD-style runtime path")
expect(disk_manifest_filename_for_path("/usr/bin/hello-world")).to_equal("HELLO.APP")
```

</details>

#### maps hello world to the packaged FAT32 manifest name

- maps hello world to the packaged FAT32 manifest name
   - Expected: disk_manifest_filename_for_path("/sys/apps/hello_world") equals `HELLO.APP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps hello world to the packaged FAT32 manifest name")
expect(disk_manifest_filename_for_path("/sys/apps/hello_world")).to_equal("HELLO.APP")
```

</details>

#### maps file manager from the FreeBSD-style runtime path

- maps file manager from the FreeBSD-style runtime path
   - Expected: disk_manifest_filename_for_path("/usr/bin/file-manager") equals `FILEMAN.APP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps file manager from the FreeBSD-style runtime path")
expect(disk_manifest_filename_for_path("/usr/bin/file-manager")).to_equal("FILEMAN.APP")
```

</details>

#### maps file manager to the packaged FAT32 manifest name

- maps file manager to the packaged FAT32 manifest name
   - Expected: disk_manifest_filename_for_path("/sys/apps/file_manager") equals `FILEMAN.APP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps file manager to the packaged FAT32 manifest name")
expect(disk_manifest_filename_for_path("/sys/apps/file_manager")).to_equal("FILEMAN.APP")
```

</details>

#### maps shell from the FreeBSD-style runtime path

- maps shell from the FreeBSD-style runtime path
   - Expected: disk_manifest_filename_for_path("/bin/shell") equals `SHELL.APP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps shell from the FreeBSD-style runtime path")
expect(disk_manifest_filename_for_path("/bin/shell")).to_equal("SHELL.APP")
```

</details>

#### maps shell to the packaged FAT32 manifest name

- maps shell to the packaged FAT32 manifest name
   - Expected: disk_manifest_filename_for_path("/sys/apps/shell") equals `SHELL.APP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps shell to the packaged FAT32 manifest name")
expect(disk_manifest_filename_for_path("/sys/apps/shell")).to_equal("SHELL.APP")
```

</details>

#### maps smux from the runtime and sys-app paths

- maps smux from the runtime and sys-app paths
   - Expected: disk_manifest_filename_for_path("/usr/bin/smux") equals `SMUX.APP`
   - Expected: disk_manifest_filename_for_path("/sys/apps/smux") equals `SMUX.APP`
   - Expected: disk_manifest_filename_for_path("/sys/apps/smux.smf") equals `SMUX.APP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps smux from the runtime and sys-app paths")
expect(disk_manifest_filename_for_path("/usr/bin/smux")).to_equal("SMUX.APP")
expect(disk_manifest_filename_for_path("/sys/apps/smux")).to_equal("SMUX.APP")
expect(disk_manifest_filename_for_path("/sys/apps/smux.smf")).to_equal("SMUX.APP")
```

</details>

#### maps AI CLI app paths to their staged manifest names

- maps AI CLI app paths to their staged manifest names
   - Expected: disk_manifest_filename_for_path("/usr/bin/codex") equals `CODEX.APP`
   - Expected: disk_manifest_filename_for_path("/sys/apps/codex") equals `CODEX.APP`
   - Expected: disk_manifest_filename_for_path("/sys/apps/claude.smf") equals `CLAUDE.APP`
   - Expected: disk_manifest_filename_for_path("/usr/bin/gemini") equals `GEMINI.APP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps AI CLI app paths to their staged manifest names")
expect(disk_manifest_filename_for_path("/usr/bin/codex")).to_equal("CODEX.APP")
expect(disk_manifest_filename_for_path("/sys/apps/codex")).to_equal("CODEX.APP")
expect(disk_manifest_filename_for_path("/sys/apps/claude.smf")).to_equal("CLAUDE.APP")
expect(disk_manifest_filename_for_path("/usr/bin/gemini")).to_equal("GEMINI.APP")
```

</details>

#### returns empty for unknown paths

- returns empty for unknown paths
   - Expected: disk_manifest_filename_for_path("/sys/apps/missing") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for unknown paths")
expect(disk_manifest_filename_for_path("/sys/apps/missing")).to_equal("")
```

</details>

#### parses the resident entry symbol from the manifest body

- parses the resident entry symbol from the manifest body
   - Expected: parse_disk_launch_entry_name(content) equals `browser_demo_remote_main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the resident entry symbol from the manifest body")
val content = "kind=resident_remote_app\nentry=browser_demo_remote_main\napp_id=/sys/apps/browser_demo\n"
expect(parse_disk_launch_entry_name(content)).to_equal("browser_demo_remote_main")
```

</details>

#### ignores comments and blank lines

- ignores comments and blank lines
   - Expected: parse_disk_launch_entry_name(content) equals `browser_demo_remote_main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores comments and blank lines")
val content = "# comment\n\nentry=browser_demo_remote_main\n"
expect(parse_disk_launch_entry_name(content)).to_equal("browser_demo_remote_main")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/loader/disk_launch_manifest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Disk launch manifest for resident-manifest launch.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6c622825defd9d6c5c32310033a2efec312dabd1232b35e1f4fc35bb64b70ace`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6c622825defd9d6c5c32310033a2efec312dabd1232b35e1f4fc35bb64b70ace`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6c622825defd9d6c5c32310033a2efec312dabd1232b35e1f4fc35bb64b70ace`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/loader/disk_launch_manifest_spec.spl
mirror: doc/06_spec/unit/os/kernel/loader/disk_launch_manifest_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/loader/disk_launch_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/loader/disk_launch_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/loader/disk_launch_manifest_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps browser demo from the FreeBSD-style runtime path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/disk_launch_manifest_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps browser demo to the packaged FAT32 manifest name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/disk_launch_manifest_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps browser demo SMF package to the packaged FAT32 manifest name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
