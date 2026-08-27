# Simpleos Desktop With Apps Framebuffer Specification

> Tests covering SimpleOS desktop framebuffer with apps (SYS-GUI-006).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Desktop With Apps Framebuffer Specification

## Scenarios

### SimpleOS desktop framebuffer with apps (SYS-GUI-006)

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

#### boots desktop, waits for remote-grouping:ok, captures with-apps baseline

- boots desktop, waits for remote-grouping:ok, captures with-apps baseline
   - Expected: _build_once(target) is true
   - Expected: file_exists(target.output) is true
   - Expected: _live_with_apps_framebuffer_capture_enabled() is false
   - Expected: file_exists(target.output) is true
   - Expected: can_run_target(target) is false
   - Expected: _run_live_capture(target, qmp_socket, serial_log, capture_ppm, baseline_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots desktop, waits for remote-grouping:ok, captures with-apps baseline")
val target = _desktop_target()
expect(_build_once(target)).to_equal(true)
expect(file_exists(target.output)).to_equal(true)

if not _live_with_apps_framebuffer_capture_enabled():
    print "[simpleos_desktop_with_apps_fb_spec] live framebuffer capture disabled; set SIMPLEOS_QEMU_DESKTOP_WITH_APPS_FRAMEBUFFER_LIVE=1 to run"
    expect(_live_with_apps_framebuffer_capture_enabled()).to_equal(false)
elif not ensure_desktop_disk_image():
    print "[simpleos_desktop_with_apps_fb_spec] disk image unavailable, skipping live capture"
    expect(file_exists(target.output)).to_equal(true)
elif not can_run_target(target):
    print "[simpleos_desktop_with_apps_fb_spec] qemu-system-x86_64 not available, skipping live capture"
    expect(can_run_target(target)).to_equal(false)
else:
    val qmp_socket = "/tmp/simpleos_desktop_with_apps_qmp.sock"
    val serial_log = "build/os/simpleos_desktop_with_apps_qemu_serial.log"
    val capture_ppm = "/tmp/simpleos_desktop_with_apps_capture.ppm"
    val baseline_dir = "test/baselines/simpleos_desktop_with_apps_framebuffer"
    val baseline_path = "{baseline_dir}/desktop_with_apps_scene.ppm"

    dir_create_all(baseline_dir)
    dir_create_all("build/os")

    expect(_run_live_capture(target, qmp_socket, serial_log, capture_ppm, baseline_path)).to_equal(true)
```

</details>

#### has a baseline directory for simpleos_desktop_with_apps_framebuffer captures

- has a baseline directory for simpleos_desktop_with_apps_framebuffer captures
   - Expected: file_exists(baseline_dir) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has a baseline directory for simpleos_desktop_with_apps_framebuffer captures")
val baseline_dir = "test/baselines/simpleos_desktop_with_apps_framebuffer"
dir_create_all(baseline_dir)
expect(file_exists(baseline_dir)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_desktop_with_apps_framebuffer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS desktop framebuffer with apps (SYS-GUI-006).
- SimpleOS desktop framebuffer with apps (SYS-GUI-006)

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

- Canonical SPipe generation for source `3047fa18f1dc9f5fafb99ee6f281516b1e2d2df907d728294d2b8d6e0aa482e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3047fa18f1dc9f5fafb99ee6f281516b1e2d2df907d728294d2b8d6e0aa482e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3047fa18f1dc9f5fafb99ee6f281516b1e2d2df907d728294d2b8d6e0aa482e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/os/simpleos_desktop_with_apps_framebuffer_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_desktop_with_apps_framebuffer_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/simpleos_desktop_with_apps_framebuffer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_desktop_with_apps_framebuffer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_desktop_with_apps_framebuffer_spec.spl:209:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds desktop_e2e_entry.spl into a baremetal kernel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_desktop_with_apps_framebuffer_spec.spl:245:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has a baseline directory for simpleos_desktop_with_apps_framebuffer captures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
