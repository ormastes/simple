# Primary Userland Host Specification

> Tests covering primary SimpleOS userland host acceptance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Primary Userland Host Specification

## Scenarios

### primary SimpleOS userland host acceptance

#### serves useful administration inspection without an external action

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- serves useful administration inspection without an external action
   - Expected: result.disposition equals `PrimaryUserlandDisposition.Completed`
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("serves useful administration inspection without an external action")
val result = primary_userland_dispatch_v1(
    PrimaryUserlandCategory.Administration, fixture(), ["status"])
expect(result.disposition).to_equal(PrimaryUserlandDisposition.Completed)
expect(result.exit_code).to_equal(0)
expect(result.output).to_contain("host=simpleos-test")
expect(result.output).to_contain("user=root")
expect(result.external_action_attempted).to_be(false)
```

</details>

#### lists archive contents supplied by the canonical host snapshot

- lists archive contents supplied by the canonical host snapshot
   - Expected: result.output equals `["etc/config.sdn", "usr/bin/app"]`
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("lists archive contents supplied by the canonical host snapshot")
val result = primary_userland_dispatch_v1(
    PrimaryUserlandCategory.Archive, fixture(), ["list"])
expect(result.output).to_equal(["etc/config.sdn", "usr/bin/app"])
expect(result.exit_code).to_equal(0)
```

</details>

#### lists network interfaces without pretending to transmit packets

- lists network interfaces without pretending to transmit packets
   - Expected: result.output equals `["lo", "eth0"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("lists network interfaces without pretending to transmit packets")
val result = primary_userland_dispatch_v1(
    PrimaryUserlandCategory.Network, fixture(), ["interfaces"])
expect(result.output).to_equal(["lo", "eth0"])
expect(result.external_action_attempted).to_be(false)
```

</details>

#### lists installed packages from a bounded host snapshot

- lists installed packages from a bounded host snapshot
   - Expected: result.output equals `["base", "shell"]`
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("lists installed packages from a bounded host snapshot")
val result = primary_userland_dispatch_v1(
    PrimaryUserlandCategory.Package, fixture(), ["list"])
expect(result.output).to_equal(["base", "shell"])
expect(result.exit_code).to_equal(0)
```

</details>

#### truthfully rejects unprovided mutation and external I/O capabilities

- truthfully rejects unprovided mutation and external I/O capabilities
   - Expected: admin.disposition equals `PrimaryUserlandDisposition.Unsupported`
   - Expected: archive.disposition equals `PrimaryUserlandDisposition.Unsupported`
   - Expected: network.disposition equals `PrimaryUserlandDisposition.Unsupported`
   - Expected: package.disposition equals `PrimaryUserlandDisposition.Unsupported`
   - Expected: admin.exit_code equals `69`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("truthfully rejects unprovided mutation and external I/O capabilities")
val admin = primary_userland_dispatch_v1(
    PrimaryUserlandCategory.Administration, fixture(), ["reboot"])
val archive = primary_userland_dispatch_v1(
    PrimaryUserlandCategory.Archive, fixture(), ["create"])
val network = primary_userland_dispatch_v1(
    PrimaryUserlandCategory.Network, fixture(), ["ping"])
val package = primary_userland_dispatch_v1(
    PrimaryUserlandCategory.Package, fixture(), ["install"])
expect(admin.disposition).to_equal(PrimaryUserlandDisposition.Unsupported)
expect(archive.disposition).to_equal(PrimaryUserlandDisposition.Unsupported)
expect(network.disposition).to_equal(PrimaryUserlandDisposition.Unsupported)
expect(package.disposition).to_equal(PrimaryUserlandDisposition.Unsupported)
expect(admin.exit_code).to_equal(69)
expect(network.external_action_attempted).to_be(false)
```

</details>

#### rejects oversized host snapshots before any category handler runs

- rejects oversized host snapshots before any category handler runs
   - Expected: result.disposition equals `PrimaryUserlandDisposition.Invalid`
   - Expected: result.exit_code equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects oversized host snapshots before any category handler runs")
var entries: [text] = []
var i: i64 = 0
while i <= PRIMARY_USERLAND_MAX_ITEMS_V1:
    entries.push("entry-{i}")
    i = i + 1
val oversized = PrimaryUserlandHostSnapshotV1(
    hostname: "host", current_user: "user", network_interfaces: [],
    installed_packages: [], archive_entries: entries)
val result = primary_userland_dispatch_v1(
    PrimaryUserlandCategory.Archive, oversized, ["list"])
expect(result.disposition).to_equal(PrimaryUserlandDisposition.Invalid)
expect(result.exit_code).to_equal(2)
expect(result.external_action_attempted).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tools/primary_userland_host_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering primary SimpleOS userland host acceptance.
- primary SimpleOS userland host acceptance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `a40a86ba9cdd03ad5d0658e91ea5bca9c01106a63b5b898138aadba29892322e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a40a86ba9cdd03ad5d0658e91ea5bca9c01106a63b5b898138aadba29892322e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a40a86ba9cdd03ad5d0658e91ea5bca9c01106a63b5b898138aadba29892322e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/tools/primary_userland_host_spec.spl
mirror: doc/06_spec/01_unit/os/tools/primary_userland_host_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tools/primary_userland_host_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tools/primary_userland_host_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/tools/primary_userland_host_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/tools/primary_userland_host_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serves useful administration inspection without an external action' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tools/primary_userland_host_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists archive contents supplied by the canonical host snapshot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tools/primary_userland_host_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lists network interfaces without pretending to transmit packets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
