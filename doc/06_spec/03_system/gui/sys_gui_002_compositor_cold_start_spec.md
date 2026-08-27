# Sys Gui 002 Compositor Cold Start Specification

> Tests covering SimpleOS compositor cold-start framebuffer baseline (SYS-GUI-002).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sys Gui 002 Compositor Cold Start Specification

## Scenarios

### SimpleOS compositor cold-start framebuffer baseline (SYS-GUI-002)

#### builds desktop_e2e_entry.spl into a baremetal kernel

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds desktop_e2e_entry.spl into a baremetal kernel
   - Expected: ok is true
   - Expected: file_exists(target.output) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds desktop_e2e_entry.spl into a baremetal kernel")
val target = _desktop_target()
val ok = build_os(target)
expect(ok).to_equal(true)
expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots desktop, captures compositor-cold-start frame, matches baseline

- boots desktop, captures compositor-cold-start frame, matches baseline
   - Expected: build_os(target) is true
   - Expected: file_exists(target.output) is true
   - Expected: _live_compositor_cold_start_capture_enabled() is false
   - Expected: qemu_available is false
   - Expected: _run_live_compositor_cold_start_capture(target) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots desktop, captures compositor-cold-start frame, matches baseline")
val target = _desktop_target()
expect(build_os(target)).to_equal(true)
expect(file_exists(target.output)).to_equal(true)

if not _live_compositor_cold_start_capture_enabled():
    print "[sys_gui_002_spec] live framebuffer capture disabled; set SIMPLEOS_QEMU_SYS_GUI_002_LIVE=1 to run"
    expect(_live_compositor_cold_start_capture_enabled()).to_equal(false)
else:
    val qemu_available = can_run_target(target)
    if not qemu_available:
        print "[sys_gui_002_spec] qemu-system-x86_64 not available, skipping live capture"
        expect(qemu_available).to_equal(false)
    else:
        expect(_run_live_compositor_cold_start_capture(target)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/sys_gui_002_compositor_cold_start_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS compositor cold-start framebuffer baseline (SYS-GUI-002).
- SimpleOS compositor cold-start framebuffer baseline (SYS-GUI-002)

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `63f7cc73f7d1917a00028975adfb980dfea1679a05a7123d866ea53ff63d0d2d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63f7cc73f7d1917a00028975adfb980dfea1679a05a7123d866ea53ff63d0d2d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63f7cc73f7d1917a00028975adfb980dfea1679a05a7123d866ea53ff63d0d2d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/03_system/gui/sys_gui_002_compositor_cold_start_spec.spl
mirror: doc/06_spec/03_system/gui/sys_gui_002_compositor_cold_start_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/sys_gui_002_compositor_cold_start_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/sys_gui_002_compositor_cold_start_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/sys_gui_002_compositor_cold_start_spec.spl:219:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds desktop_e2e_entry.spl into a baremetal kernel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
