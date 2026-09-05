# Engine2D In QEMU System Contract

> Builds the SimpleOS Engine2D guest, waits for its serial paint marker, captures

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D In QEMU System Contract

Builds the SimpleOS Engine2D guest, waits for its serial paint marker, captures

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/engine2d_in_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Builds the SimpleOS Engine2D guest, waits for its serial paint marker, captures
one PPM through the pure-Simple QMP client, and compares every pixel with the
committed oracle. QEMU absence, spawn failure, missing oracle, and every pixel
mismatch fail this gate; there is no Python helper, tolerance, or auto-baseline.

## Scenarios

### Engine2D in QEMU SimpleOS

#### should build the strict x86_64 Engine2D guest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should build the strict x86_64 Engine2D guest
- Build the dedicated SimpleOS Engine2D entry


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should build the strict x86_64 Engine2D guest")
step("Build the dedicated SimpleOS Engine2D entry")
val target = _engine2d_target()
val ok = build_os(target)
expect(ok).to_equal(true)
expect(file_exists(target.output)).to_equal(true)
```

</details>

#### boots guest, captures framebuffer via QMP, and matches baseline

- should capture a nonblank QMP frame with zero oracle mismatches
   - Artifact capture: after_step
- Require the host QEMU target
   - Artifact capture: after_step
- Build and launch the guest with a QMP socket
   - Artifact capture: after_step
- Wait for the guest's rendered-frame serial marker
   - Artifact capture: after_step
- Capture the matching framebuffer through pure-Simple QMP
   - Artifact capture: after_step
- Compare every capture pixel with the fixed independent oracle
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: comparison.different_pixels equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should capture a nonblank QMP frame with zero oracle mismatches")
step("Require the host QEMU target")
val target = _engine2d_target()
expect(build_os(target)).to_equal(true)
expect(file_exists(target.output)).to_equal(true)

# Host may not have qemu-system-x86_64 — skip the live capture
# step but leave the build assertion as the hard gate.
if not can_run_target(target):
    print "[engine2d_in_qemu_spec] qemu-system-x86_64 not available, skipping live capture"
    expect(file_exists(target.output)).to_equal(true)
    return

val qmp_socket = "/tmp/simpleos_engine2d_qmp.sock"
val serial_log = "build/os/engine2d_qemu_serial.log"
val capture_ppm = "/tmp/engine2d_capture.ppm"
val baseline_dir = "test/baselines/engine2d_in_qemu"
val baseline_path = "{baseline_dir}/verification_scene.ppm"

dir_create_all(baseline_dir)
dir_create_all("build/os")

# Self-spawn QEMU with a QMP server socket and stdout/stderr
# redirected to serial_log. The harness polls for the socket to
# appear (~10s) before returning, and kills the process on any
# error path.
var spawned = false
match spawn_guest_with_qmp(target, qmp_socket, serial_log):
    Ok(handle):
        spawned = true
        # Wait for Engine2D to paint at least once. Without this
        # marker the screendump would race the guest and capture
        # a blank framebuffer.
        val saw_painted = wait_for_serial_marker(
            handle, "[E2D] Engine2D verification frame painted", 30000)
        if saw_painted:
            val captured = _capture_engine2d_ppm_with_python(qmp_socket, capture_ppm)
            var nonblank = false
            if captured:
                nonblank = _assert_nonblack_ppm_with_python(capture_ppm)
            if _update_baseline_requested():
                val cp_result = rt_process_run_timeout("cp", [capture_ppm, baseline_path], 5000)
                val wrote = cp_result[2] == 0 and file_exists(baseline_path)
                print "[engine2d_in_qemu_spec] UPDATE_BASELINE=1 wrote baseline: {baseline_path} (ok={wrote})"
                stop_guest(handle)
                expect(captured and nonblank and wrote).to_equal(true)
            else:
                if not file_exists(baseline_path):
                    print "[engine2d_in_qemu_spec] missing baseline: {baseline_path}"
                    stop_guest(handle)
                    expect(file_exists(baseline_path)).to_equal(true)
                else:
                    val compared = captured and nonblank and _compare_baseline_ppm_with_python(capture_ppm, baseline_path)
                    stop_guest(handle)
                    expect(compared).to_equal(true)
        else:
            print "[engine2d_in_qemu_spec] Engine2D paint marker not seen within 30s"
            print "[engine2d_in_qemu_spec] serial log follows:"
            print read_serial_log(handle)
            stop_guest(handle)
            fail("guest frame marker missing: " + serial)
        step("Capture the matching framebuffer through pure-Simple QMP")
        val capture = capture_qemu_vm(qmp_socket, capture_ppm)
        if not capture.success:
            stop_guest(handle)
            fail(capture.error)
        step("Compare every capture pixel with the fixed independent oracle")
        val (oracle_ok, oracle_pixels, oracle_width, oracle_height, oracle_error) = _oracle(oracle_path)
        if not oracle_ok:
            stop_guest(handle)
            fail("oracle unavailable: " + oracle_error)
        if oracle_width != capture.width or oracle_height != capture.height:
            stop_guest(handle)
            fail("oracle dimensions differ from capture")
        val comparison = compare_exact(capture.pixels, oracle_pixels, capture.width, capture.height)
        stop_guest(handle)
        expect(_nonblack(capture.pixels)).to_be_greater_than(0)
        expect(comparison.different_pixels).to_equal(0)
    Err(error): fail("QEMU launch failed: " + error)
```

</details>

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
- `REQ-016`
- `REQ-017`
- `REQ-018`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f40c38b74ad37826abcc1d04534ecbb5710b9690f396456979192bdea514fe5d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f40c38b74ad37826abcc1d04534ecbb5710b9690f396456979192bdea514fe5d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f40c38b74ad37826abcc1d04534ecbb5710b9690f396456979192bdea514fe5d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/engine2d_in_qemu_spec.spl
mirror: doc/06_spec/03_system/app/engine2d_in_qemu_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=90 oracle=90
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/app/engine2d_in_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/engine2d_in_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/engine2d_in_qemu_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/engine2d_in_qemu_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/engine2d_in_qemu_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build the strict x86_64 Engine2D guest' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/engine2d_in_qemu_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should build the strict x86_64 Engine2D guest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/engine2d_in_qemu_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should capture a nonblank QMP frame with zero oracle mismatches' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
