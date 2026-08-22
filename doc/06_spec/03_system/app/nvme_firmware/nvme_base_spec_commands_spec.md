# nvme_base_spec_commands_spec

> Verifies the nvme base spec commands behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_base_spec_commands_spec

Verifies the nvme base spec commands behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/nvme_base_spec_commands.md |
| Plan | doc/03_plan/sys_test/nvme_base_spec_commands.md |
| Design | N/A |
| Research | doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md |
| Source | `test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the nvme base spec commands behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### NVMe base-spec command floor

#### should identify the controller and enforce IO queue lifecycle rules

- Verify: should identify the controller and enforce IO queue lifecycle rules
- Run the host-facing controller lifecycle demo
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario`
- Verify Identify Controller and Identify Namespace results
- Verify legal queue order and invalid binding rejection


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005
step("Verify: should identify the controller and enforce IO queue lifecycle rules")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Run the host-facing controller lifecycle demo")
val (out, err, code) = _run_simple(FW + "/nvme_main.spl")
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario

step("Verify Identify Controller and Identify Namespace results")
expect(out).to_contain("identify controller ok")
expect(out).to_contain("controller reports max IO queues")
expect(out).to_contain("namespace size == LBA_COUNT")

step("Verify legal queue order and invalid binding rejection")
expect(out).to_contain("create IO CQ 1")
expect(out).to_contain("create IO SQ 1 -> CQ 1")
expect(out).to_contain("SQ -> missing CQ rejected")
expect(out).to_contain("delete bound CQ rejected")
expect(out).to_contain("delete SQ 1 ok")
expect(out).to_contain("delete CQ 1 ok")
_expect_no_fail_marker(out, "host controller lifecycle")
```

</details>

#### should pass the rv32-compatible admin and NVM command floor

- Verify: should pass the rv32-compatible admin and NVM command floor
- Run the scalar firmware command checker
   - Expected: code equals `0)  # oracle: pinned constant asserted by this scenario`
- Verify admin, queue, opcode, and NVM command families
- Verify reserved-field, namespace, Abort, and backpressure guards


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005
step("Verify: should pass the rv32-compatible admin and NVM command floor")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Run the scalar firmware command checker")
val (out, err, code) = _run_simple(RV32 + "/base_spec_check.spl")
expect(code).to_equal(0)  # oracle: pinned constant asserted by this scenario

step("Verify admin, queue, opcode, and NVM command families")
expect(out).to_contain("NVME-ADMIN-IDENTIFY-FEATURES-LOG-FORMAT-FW PASS")
expect(out).to_contain("NVME-QUEUE-PHASE-CREATE-DELETE PASS")
expect(out).to_contain("NVME-HIL-OPCODE-BOUNDS PASS")
expect(out).to_contain("NVME-NVM-READ-WRITE-ZEROES-DSM-TRIM PASS")
expect(out).to_contain("NVME-NVM-FLUSH PASS")

step("Verify reserved-field, namespace, Abort, and backpressure guards")
expect(out).to_contain("NVME-FEATURE-RESERVED-FIELD-GUARD PASS")
expect(out).to_contain("NVME-NAMESPACE-RESERVED-FIELD-GUARD PASS")
expect(out).to_contain("NVME-ABORT-BACKPRESSURE PASS")
expect(out).to_contain("NVME BASE SPEC CHECKS PASS")
_expect_no_fail_marker(out, "rv32 command floor")
```

</details>

#### should fail closed when the selected Simple runtime is missing

- Verify: should fail closed when the selected Simple runtime is missing
- Select a runtime path that cannot exist
- Verify the missing runtime cannot produce passing evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-001 REQ-002 REQ-003 REQ-004 REQ-005
step("Verify: should fail closed when the selected Simple runtime is missing")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Select a runtime path that cannot exist")
val (out, err, code) = _run("NVME_RV32_SIMPLE_BIN=/definitely/missing/simple; \"$NVME_RV32_SIMPLE_BIN\" run " + RV32 + "/base_spec_check.spl")

step("Verify the missing runtime cannot produce passing evidence")
expect(code).to_be_greater_than(0)
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


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/nvme_base_spec_commands.md`
- **Plan:** `doc/03_plan/sys_test/nvme_base_spec_commands.md`
- **Research:** `doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `06fb7bfad2fec2cfddc6e85e99c65edda9c83a23d7d712d9ac37e96c4cfdcc2c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `06fb7bfad2fec2cfddc6e85e99c65edda9c83a23d7d712d9ac37e96c4cfdcc2c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `06fb7bfad2fec2cfddc6e85e99c65edda9c83a23d7d712d9ac37e96c4cfdcc2c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl
mirror: doc/06_spec/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should identify the controller and enforce IO queue lifecycle rules' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pass the rv32-compatible admin and NVM command floor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl:116:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed when the selected Simple runtime is missing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
