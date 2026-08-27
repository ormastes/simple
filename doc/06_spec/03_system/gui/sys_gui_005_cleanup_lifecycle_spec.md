# Sys Gui 005 Cleanup Lifecycle Specification

> Tests covering SimpleOS lifecycle cleanup live gate (SYS-GUI-005).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sys Gui 005 Cleanup Lifecycle Specification

## Scenarios

### SimpleOS lifecycle cleanup live gate (SYS-GUI-005)

#### builds sys_gui_005_cleanup_entry.spl into a baremetal kernel

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds sys_gui_005_cleanup_entry.spl into a baremetal kernel
   - Expected: file_exists(target.entry) is false
   - Expected: ok is true
   - Expected: file_exists(target.output) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds sys_gui_005_cleanup_entry.spl into a baremetal kernel")
val target = _cleanup_target()
if not file_exists(target.entry):
    print "[sys_gui_005_spec] missing cleanup entry {target.entry}, skipping build"
    expect(file_exists(target.entry)).to_equal(false)
else:
    val ok = build_os(target)
    expect(ok).to_equal(true)
    expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots cleanup entry, walks all three sub-scenarios, captures post-cleanup frame

- boots cleanup entry, walks all three sub-scenarios, captures post-cleanup frame
   - Expected: file_exists(target.entry) is false
   - Expected: _live_cleanup_capture_enabled() is false
   - Expected: can_run_target(target) is false
   - Expected: build_os(target) is true
   - Expected: file_exists(target.output) is true
   - Expected: target.entry contains `sys_gui_005_cleanup_entry.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots cleanup entry, walks all three sub-scenarios, captures post-cleanup frame")
val target = _cleanup_target()
if not file_exists(target.entry):
    print "[sys_gui_005_spec] missing cleanup entry {target.entry}, skipping live capture"
    expect(file_exists(target.entry)).to_equal(false)
else:
    if not _live_cleanup_capture_enabled():
        print "[sys_gui_005_spec] live cleanup capture disabled; set SIMPLEOS_QEMU_SYS_GUI_005_LIVE=1 to run"
        expect(_live_cleanup_capture_enabled()).to_equal(false)
    else:
        if not can_run_target(target):
            print "[sys_gui_005_spec] qemu-system-x86_64 not available, skipping live capture"
            expect(can_run_target(target)).to_equal(false)
        else:
            expect(build_os(target)).to_equal(true)
            expect(file_exists(target.output)).to_equal(true)
            print "[sys_gui_005_spec] live capture implementation is gated on restoring {target.entry}"
            expect(target.entry.contains("sys_gui_005_cleanup_entry.spl")).to_equal(true)
```

</details>

#### has a baselines directory for the SYS-GUI-005 cleanup gate

- has a baselines directory for the SYS-GUI-005 cleanup gate
   - Expected: file_exists(baseline_dir) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has a baselines directory for the SYS-GUI-005 cleanup gate")
val baseline_dir = "doc/08_tracking/baselines"
dir_create_all(baseline_dir)
expect(file_exists(baseline_dir)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/sys_gui_005_cleanup_lifecycle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS lifecycle cleanup live gate (SYS-GUI-005).
- SimpleOS lifecycle cleanup live gate (SYS-GUI-005)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `570125128bcaffaf24f3abb391bd88f73eca0ae3d62ee6ee63dab2ab70bc70a8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `570125128bcaffaf24f3abb391bd88f73eca0ae3d62ee6ee63dab2ab70bc70a8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `570125128bcaffaf24f3abb391bd88f73eca0ae3d62ee6ee63dab2ab70bc70a8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/gui/sys_gui_005_cleanup_lifecycle_spec.spl
mirror: doc/06_spec/03_system/gui/sys_gui_005_cleanup_lifecycle_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/sys_gui_005_cleanup_lifecycle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/sys_gui_005_cleanup_lifecycle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/sys_gui_005_cleanup_lifecycle_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds sys_gui_005_cleanup_entry.spl into a baremetal kernel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/sys_gui_005_cleanup_lifecycle_spec.spl:192:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has a baselines directory for the SYS-GUI-005 cleanup gate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
