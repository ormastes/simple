# SimpleOS Desktop Framebuffer Baseline Spec

> Builds the desktop target and, when live capture is enabled, compares the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Desktop Framebuffer Baseline Spec

Builds the desktop target and, when live capture is enabled, compares the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_desktop_framebuffer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Builds the desktop target and, when live capture is enabled, compares the
captured framebuffer against the committed baseline.

## Scenarios

### SimpleOS desktop framebuffer baseline (SYS-GUI-006)

#### builds desktop_e2e_entry.spl into a baremetal kernel when live capture is enabled

- builds desktop_e2e_entry.spl into a baremetal kernel when live capture is enabled
   - Expected: ok is true
   - Expected: file_exists(target.output) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds desktop_e2e_entry.spl into a baremetal kernel when live capture is enabled")
val target = _desktop_target()
if not _live_framebuffer_capture_enabled():
    print "[simpleos_desktop_fb_spec] desktop build skipped; set SIMPLEOS_QEMU_DESKTOP_FRAMEBUFFER_LIVE=1 or UPDATE_BASELINE=1 to run"
    expect(target.output).to_contain("desktop")
else:
    val ok = build_os(target)
    expect(ok).to_equal(true)
    expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots desktop, captures framebuffer via QMP, and matches baseline

- boots desktop, captures framebuffer via QMP, and matches baseline
   - Expected: built is true
   - Expected: file_exists(target.output) is true
   - Expected: file_exists(target.output) is true
   - Expected: file_exists(target.output) is true
   - Expected: capture_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots desktop, captures framebuffer via QMP, and matches baseline")
val target = _desktop_target()
if not _live_framebuffer_capture_enabled():
    print "[simpleos_desktop_fb_spec] live framebuffer capture disabled; set SIMPLEOS_QEMU_DESKTOP_FRAMEBUFFER_LIVE=1 to run"
    expect(target.qemu_system).to_contain("qemu-system")
else:
    # Always rebuild here so live compare/update never captures stale
    # output left by an earlier run.
    val built = _build_once(target)
    expect(built).to_equal(true)
    if not built:
        print "[simpleos_desktop_fb_spec] desktop build failed; live capture not attempted"
    else:
        expect(file_exists(target.output)).to_equal(true)

        val disk_ok = ensure_desktop_disk_image()
        if not disk_ok:
            print "[simpleos_desktop_fb_spec] disk image unavailable, skipping live capture"
            expect(file_exists(target.output)).to_equal(true)
        else:
            # Host may not have qemu-system-x86_64 installed — skip the live
            # capture step but keep the build assertion as the hard gate so
            # a missing QEMU never silently hides a build regression.
            if not can_run_target(target):
                print "[simpleos_desktop_fb_spec] qemu-system-x86_64 not available, skipping live capture"
                expect(file_exists(target.output)).to_equal(true)
            else:
                val qmp_socket = "/tmp/simpleos_desktop_qmp.sock"
                val serial_log = "build/os/simpleos_desktop_qemu_serial.log"
                # QEMU's screendump path handling is host-policy sensitive; use /tmp
                # alongside the QMP socket to avoid repo-worktree permission drift.
                val capture_ppm = "/tmp/simpleos_desktop_capture.ppm"
                val baseline_dir = "test/baselines/simpleos_desktop_framebuffer"
                val baseline_path = "{baseline_dir}/desktop_scene.ppm"

                dir_create_all(baseline_dir)
                dir_create_all("build/os")

                val capture_ok = _run_live_capture(target, qmp_socket, serial_log, capture_ppm, baseline_path)
                expect(capture_ok).to_equal(true)
```

</details>

#### has a baseline directory for simpleos_desktop_framebuffer captures

- has a baseline directory for simpleos_desktop_framebuffer captures
   - Expected: file_exists(baseline_dir) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has a baseline directory for simpleos_desktop_framebuffer captures")
val baseline_dir = "test/baselines/simpleos_desktop_framebuffer"
dir_create_all(baseline_dir)
expect(file_exists(baseline_dir)).to_equal(true)
```

</details>

#### has a committed non-empty desktop framebuffer baseline

- has a committed non-empty desktop framebuffer baseline
   - Expected: ok is true
   - Expected: width equals `1024`
   - Expected: height equals `768`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has a committed non-empty desktop framebuffer baseline")
val baseline_path = "test/baselines/simpleos_desktop_framebuffer/desktop_scene.ppm"
val (ok, pixels, width, height, err) = _read_baseline_ppm(baseline_path)
if not ok:
    print "[simpleos_desktop_fb_spec] invalid baseline: {err}"
expect(ok).to_equal(true)
expect(width).to_equal(1024)
expect(height).to_equal(768)
expect(_non_black_count(pixels)).to_be_greater_than(0)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7a8d604f2eb433b786630430a8a911c4f732f354f6b8ca740e2f2a6d5218a0e4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7a8d604f2eb433b786630430a8a911c4f732f354f6b8ca740e2f2a6d5218a0e4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7a8d604f2eb433b786630430a8a911c4f732f354f6b8ca740e2f2a6d5218a0e4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/03_system/os/simpleos_desktop_framebuffer_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_desktop_framebuffer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=65 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/simpleos_desktop_framebuffer_spec.md:1:1: warning SSDOC-EVD-003 [evidence] (-15): source captures are not rendered as manual evidence
  why: Retained evidence must be visible or linked from the professional manual.
  improve: Select a supported evidence display and regenerate.
doc/06_spec/03_system/os/simpleos_desktop_framebuffer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_desktop_framebuffer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_desktop_framebuffer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/simpleos_desktop_framebuffer_spec.spl:404:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has a baseline directory for simpleos_desktop_framebuffer captures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_desktop_framebuffer_spec.spl:411:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has a committed non-empty desktop framebuffer baseline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
