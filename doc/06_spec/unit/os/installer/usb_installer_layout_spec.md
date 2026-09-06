# Usb Installer Layout Specification

> Tests covering USB installer layout helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Usb Installer Layout Specification

## Scenarios

### USB installer layout helpers

#### detects at least the QEMU virtio target

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects at least the QEMU virtio target
   - Expected: disks[0].path equals `/dev/vda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects at least the QEMU virtio target")
val disks = detect_disks()
expect(disks.len()).to_be_greater_than(0)
expect(disks[0].path).to_equal("/dev/vda")
```

</details>

#### uses an EFI plus root plus swap default plan

- uses an EFI plus root plus swap default plan
   - Expected: plan.efi_size_mb equals `256`
   - Expected: plan.root_size_mb equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses an EFI plus root plus swap default plan")
val disks = detect_disks()
val plan = default_partition_plan(disks[0])
expect(plan.efi_size_mb).to_equal(256)
expect(plan.root_size_mb).to_equal(0)
expect(plan.swap_size_mb).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/installer/usb_installer_layout_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering USB installer layout helpers.
- USB installer layout helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `f7eebc9d85a677758cb727cae491d791f8ae30c4139e2b7eb712609da33bf8c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7eebc9d85a677758cb727cae491d791f8ae30c4139e2b7eb712609da33bf8c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7eebc9d85a677758cb727cae491d791f8ae30c4139e2b7eb712609da33bf8c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/installer/usb_installer_layout_spec.spl
mirror: doc/06_spec/unit/os/installer/usb_installer_layout_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/installer/usb_installer_layout_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/installer/usb_installer_layout_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/installer/usb_installer_layout_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/installer/usb_installer_layout_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects at least the QEMU virtio target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/installer/usb_installer_layout_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses an EFI plus root plus swap default plan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
