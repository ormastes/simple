# Arm64 Fs Exec Launch Capability Specification

> Tests covering ARM64 filesystem payload launch capabilities.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm64 Fs Exec Launch Capability Specification

## Scenarios

### ARM64 filesystem payload launch capabilities

#### allows only the prepared network and file operations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allows only the prepared network and file operations
   - Expected: mgr.check(task, CapabilityKind.NetConnect(port: 0)) is true
   - Expected: mgr.check(task, CapabilityKind.NetListen(port: 0)) is true
   - Expected: mgr.check_file_access(task, "/usr/bin/simple", "rx") is true
   - Expected: mgr.check_file_access(task, "/hello.spl", "r") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("allows only the prepared network and file operations")
var mgr = CapabilityManager.new()
val task = TaskId(id: 41u64)
val caps = arm64_fs_exec_launch_caps(
    "/usr/bin/simple", ["/usr/bin/simple", "/hello.spl", "--check"], task.id)
mgr.init_task(task, caps)

expect(mgr.check(task, CapabilityKind.NetConnect(port: 0))).to_equal(true)
expect(mgr.check(task, CapabilityKind.NetListen(port: 0))).to_equal(true)
expect(mgr.check_file_access(task, "/usr/bin/simple", "rx")).to_equal(true)
expect(mgr.check_file_access(task, "/hello.spl", "r")).to_equal(true)
```

</details>

#### denies undeclared paths, writes, raw network, and process spawning

- denies undeclared paths, writes, raw network, and process spawning
   - Expected: mgr.check_file_access(task, "/etc/passwd", "r") is false
   - Expected: mgr.check_file_access(task, "/hello.spl.bak", "r") is false
   - Expected: mgr.check_file_access(task, "/hello.spl", "w") is false
   - Expected: mgr.check(task, CapabilityKind.NetRaw) is false
   - Expected: mgr.check(task, CapabilityKind.ProcessSpawn) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("denies undeclared paths, writes, raw network, and process spawning")
var mgr = CapabilityManager.new()
val task = TaskId(id: 42u64)
val caps = arm64_fs_exec_launch_caps(
    "/usr/bin/simple", ["/usr/bin/simple", "/hello.spl", "--check"], task.id)
mgr.init_task(task, caps)

expect(mgr.check_file_access(task, "/etc/passwd", "r")).to_equal(false)
expect(mgr.check_file_access(task, "/hello.spl.bak", "r")).to_equal(false)
expect(mgr.check_file_access(task, "/hello.spl", "w")).to_equal(false)
expect(mgr.check(task, CapabilityKind.NetRaw)).to_equal(false)
expect(mgr.check(task, CapabilityKind.ProcessSpawn)).to_equal(false)
```

</details>

#### keeps the launch pouch pledged and non-ambient

- keeps the launch pouch pledged and non-ambient
   - Expected: caps.is_pledged is true
   - Expected: caps.caps.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps the launch pouch pledged and non-ambient")
val caps = arm64_fs_exec_launch_caps("/FSEXEC.ELF", ["/FSEXEC.ELF"], 43u64)
expect(caps.is_pledged).to_equal(true)
expect(caps.caps.len()).to_equal(4)
```

</details>

#### grants the server only its exact documents, credential, and persistence names

- grants the server only its exact documents, credential, and persistence names
   - Expected: mgr.check_file_access(task, "/SYS/SERVER.HTM", "r") is true
   - Expected: mgr.check_file_access(task, "/SYS/SRVDB.KEY", "r") is true
   - Expected: mgr.check_file_access(task, "/SERVER.SDN", "rwc") is true
   - Expected: mgr.check_file_access(task, "/SERVER.SDN.lock", "rwc") is true
   - Expected: mgr.check_file_access(task, "/SERVER.SDN.tmp", "rwc") is true
   - Expected: mgr.check_file_access(task, "/SERVER.SDN.wal", "rwc") is true
   - Expected: mgr.check_file_access(task, "/SERVER.SDN.wal.lock", "rwc") is true
   - Expected: mgr.check_file_access(task, "/SERVER.SDN.wal.tmp", "rwc") is true
   - Expected: mgr.check_file_access(task, "/SYS/OTHER.HTM", "r") is false
   - Expected: mgr.check_file_access(task, "/SERVER.SDN.backup", "r") is false
   - Expected: mgr.check_file_access(task, "/", "rwc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("grants the server only its exact documents, credential, and persistence names")
var mgr = CapabilityManager.new()
val task = TaskId(id: 44u64)
mgr.init_task(task, arm64_fs_exec_launch_caps(
    "/SERVERS.ELF", ["/SERVERS.ELF"], task.id))

expect(mgr.check_file_access(task, "/SYS/SERVER.HTM", "r")).to_equal(true)
expect(mgr.check_file_access(task, "/SYS/SRVDB.KEY", "r")).to_equal(true)
expect(mgr.check_file_access(task, "/SERVER.SDN", "rwc")).to_equal(true)
expect(mgr.check_file_access(task, "/SERVER.SDN.lock", "rwc")).to_equal(true)
expect(mgr.check_file_access(task, "/SERVER.SDN.tmp", "rwc")).to_equal(true)
expect(mgr.check_file_access(task, "/SERVER.SDN.wal", "rwc")).to_equal(true)
expect(mgr.check_file_access(task, "/SERVER.SDN.wal.lock", "rwc")).to_equal(true)
expect(mgr.check_file_access(task, "/SERVER.SDN.wal.tmp", "rwc")).to_equal(true)
expect(mgr.check_file_access(task, "/SYS/OTHER.HTM", "r")).to_equal(false)
expect(mgr.check_file_access(task, "/SERVER.SDN.backup", "r")).to_equal(false)
expect(mgr.check_file_access(task, "/", "rwc")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/arm64_fs_exec_launch_capability_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ARM64 filesystem payload launch capabilities.
- ARM64 filesystem payload launch capabilities

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `48a749721395bbead6e6a260ab7e5716a77d7b17524b8ff8666d97d5739483a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `48a749721395bbead6e6a260ab7e5716a77d7b17524b8ff8666d97d5739483a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `48a749721395bbead6e6a260ab7e5716a77d7b17524b8ff8666d97d5739483a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/kernel/loader/arm64_fs_exec_launch_capability_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/arm64_fs_exec_launch_capability_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/arm64_fs_exec_launch_capability_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/arm64_fs_exec_launch_capability_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/arm64_fs_exec_launch_capability_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/loader/arm64_fs_exec_launch_capability_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows only the prepared network and file operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/arm64_fs_exec_launch_capability_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'denies undeclared paths, writes, raw network, and process spawning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/arm64_fs_exec_launch_capability_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the launch pouch pledged and non-ambient' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
