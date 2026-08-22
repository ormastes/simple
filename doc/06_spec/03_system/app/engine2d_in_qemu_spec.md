# Engine2D In QEMU

> Verifies the engine2d in qemu behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D In QEMU

Verifies the engine2d in qemu behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/engine2d_in_qemu_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the engine2d in qemu behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Engine2D in QEMU SimpleOS

#### should build the strict x86_64 Engine2D guest

- Verify: should build the strict x86_64 Engine2D guest
- Build the dedicated SimpleOS Engine2D entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-016 REQ-017 REQ-018
step("Verify: should build the strict x86_64 Engine2D guest")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Build the dedicated SimpleOS Engine2D entry")
val target = _engine2d_target()
expect(build_os(target)).to_be(true)
expect(file_exists(target.output)).to_be(true)
```

</details>

#### should capture a nonblank QMP frame with zero oracle mismatches

- Verify: should capture a nonblank QMP frame with zero oracle mismatches
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
   - Expected: comparison.different_pixels equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-016 REQ-017 REQ-018
step("Verify: should capture a nonblank QMP frame with zero oracle mismatches")
step("Require the host QEMU target")
val target = _engine2d_target()
expect(can_run_target(target)).to_be(true)
step("Build and launch the guest with a QMP socket")
expect(build_os(target)).to_be(true)
dir_create_all("build/os")
val qmp_socket = "/tmp/simpleos_engine2d_qmp.sock"
val serial_log = "build/os/engine2d_qemu_serial.log"
val capture_ppm = "/tmp/engine2d_capture.ppm"
val oracle_path = "test/09_baselines/engine2d_in_qemu/verification_scene.ppm"
match spawn_guest_with_qmp(target, qmp_socket, serial_log):
    Ok(handle):
        step("Wait for the guest's rendered-frame serial marker")
        val painted = wait_for_serial_marker(handle, "[E2D] Engine2D verification frame painted", 30000)
        if not painted:
            val serial = read_serial_log(handle)
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
        expect(comparison.different_pixels).to_equal(0)  # oracle: pinned constant asserted by this scenario
    Err(error): fail("QEMU launch failed: " + error)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6174b89acdc0f680112b386a2ea9bc29af3e77cfe314805d3ca18bd5cb22657f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6174b89acdc0f680112b386a2ea9bc29af3e77cfe314805d3ca18bd5cb22657f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6174b89acdc0f680112b386a2ea9bc29af3e77cfe314805d3ca18bd5cb22657f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/03_system/app/engine2d_in_qemu_spec.spl
mirror: doc/06_spec/03_system/app/engine2d_in_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/engine2d_in_qemu_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/engine2d_in_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/engine2d_in_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/engine2d_in_qemu_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build the strict x86_64 Engine2D guest' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/engine2d_in_qemu_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should capture a nonblank QMP frame with zero oracle mismatches' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
