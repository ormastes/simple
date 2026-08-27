# SimpleOS WM Visible-Display Boot-Ladder Contract

> Proves that the UEFI boot ladder distinguishes an absent serial log from an

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS WM Visible-Display Boot-Ladder Contract

Proves that the UEFI boot ladder distinguishes an absent serial log from an

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/simpleos_wm_visible_display_boot_ladder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves that the UEFI boot ladder distinguishes an absent serial log from an
existing log with missing markers, and that production evaluates the ladder
only after serial-marker readiness or failure-path QEMU quiescence.

## Scenarios

### SimpleOS WM visible-display boot ladder

#### classifies absent and incomplete serial logs without launching QEMU

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies absent and incomplete serial logs without launching QEMU
- Run the bounded boot-ladder self-test
   - Expected: code equals `0`
   - Expected: stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("classifies absent and incomplete serial logs without launching QEMU")
step("Run the bounded boot-ladder self-test")
val (stdout, stderr, code) = process_run(
    "/bin/sh",
    ["-c", "sh scripts/check/check-simpleos-wm-visible-display-evidence.shs --self-test"]
)
expect(code).to_equal(0)
expect(stderr).to_equal("")
expect(stdout).to_contain("simpleos_wm_boot_ladder_self_test_absent_log=pass")
expect(stdout).to_contain("simpleos_wm_boot_ladder_self_test_marker_absent=pass")
expect(stdout).to_contain("simpleos_wm_boot_ladder_self_test_complete=pass")
expect(stdout).to_contain("simpleos_wm_boot_ladder_self_test_order=pass")
expect(stdout).to_contain("simpleos_wm_boot_ladder_self_test_status=pass")
```

</details>

#### keeps the persistent QEMU capture after the serial readiness point

- keeps the persistent QEMU capture after the serial readiness point
- Inspect the production observation order
   - Expected: script.index_of("rung \"\\[grub-uefi\\]") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps the persistent QEMU capture after the serial readiness point")
step("Inspect the production observation order")
val script = file_read("scripts/check/check-simpleos-wm-visible-display-evidence.shs")
val marker_wait = script.index_of("while [ \"$waited\" -le \"$MARKER_TIMEOUT_SECS\" ]; do")
val success_ladder = script.index_of("evaluate_boot_ladder \"serial-markers-established\"")
val qmp_capture = script.index_of("python3 - \"$QMP_SOCKET\" \"$PPM_PATH\"")
expect(marker_wait).to_be_greater_than(0)
expect(success_ladder).to_be_greater_than(marker_wait)
expect(qmp_capture).to_be_greater_than(success_ladder)
expect(script).to_contain("evaluate_boot_ladder \"failure-after-qemu-quiescence\"")
expect(script).to_contain("serial-log-not-created-at-check-time")
expect(script).to_contain("marker-absent-in-existing-serial-log")
expect(script).to_contain("boot_ladder_pending_on_fail=1")
expect(script).to_contain("simpleos_wm_visible_display_boot_ladder_observation=")
expect(script.index_of("rung \"\\[grub-uefi\\]")).to_equal(-1)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `de507c1959dca5e7eb115dcfdded5890a875acc723e5dd1202d515c102130074`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de507c1959dca5e7eb115dcfdded5890a875acc723e5dd1202d515c102130074`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de507c1959dca5e7eb115dcfdded5890a875acc723e5dd1202d515c102130074`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/check/simpleos_wm_visible_display_boot_ladder_spec.spl
mirror: doc/06_spec/03_system/check/simpleos_wm_visible_display_boot_ladder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/simpleos_wm_visible_display_boot_ladder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/simpleos_wm_visible_display_boot_ladder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/simpleos_wm_visible_display_boot_ladder_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/simpleos_wm_visible_display_boot_ladder_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies absent and incomplete serial logs without launching QEMU' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/simpleos_wm_visible_display_boot_ladder_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the persistent QEMU capture after the serial readiness point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
