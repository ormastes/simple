# nvme_baremetal_wrapper_coverage_spec

> NVMe baremetal wrapper coverage audit.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvme_baremetal_wrapper_coverage_spec

NVMe baremetal wrapper coverage audit.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/nvme_firmware/nvme_baremetal_wrapper_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

NVMe baremetal wrapper coverage audit.

The audit is not real boot evidence. It proves the wrapper-evidence surface:
RV32 and RV64 have fail-closed fake-QEMU self-tests wired into their SSpecs.

## Scenarios

### NVMe baremetal wrapper coverage audit

#### reports RV32 and RV64 wrapper coverage in default mode

- reports RV32 and RV64 wrapper coverage in default mode
- Run the default NVMe baremetal wrapper coverage audit
   - Expected: code equals `0`
- The audit proves RV32 wrapper self-test coverage
- The audit proves RV64 wrapper self-test coverage


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports RV32 and RV64 wrapper coverage in default mode")
step("Run the default NVMe baremetal wrapper coverage audit")
val (out, err, code) = _run("sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs")
expect(code).to_equal(0)

step("The audit proves RV32 wrapper self-test coverage")
expect(out).to_contain("nvme_baremetal_wrapper_rv32_self_test=pass")
expect(out).to_contain("nvme_baremetal_wrapper_rv32_spec_status=pass")

step("The audit proves RV64 wrapper self-test coverage")
expect(out).to_contain("nvme_baremetal_wrapper_coverage_status=pass")
expect(out).to_contain("nvme_baremetal_wrapper_coverage_blockers=none")
expect(out).to_contain("nvme_baremetal_wrapper_rv64_self_test=pass")
expect(out).to_contain("nvme_baremetal_wrapper_rv64_spec_status=pass")
expect(out).to_contain("STATUS: PASS nvme-baremetal-wrapper-coverage status=pass blockers=none")
_expect_no_fail_marker(out, "default wrapper coverage audit")
```

</details>

#### passes strict mode when RV32 and RV64 wrapper coverage exists

- passes strict mode when RV32 and RV64 wrapper coverage exists
- Run strict mode after both wrappers have fail-closed self-test coverage
   - Expected: code equals `0`
- Strict mode reports a complete wrapper coverage pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes strict mode when RV32 and RV64 wrapper coverage exists")
step("Run strict mode after both wrappers have fail-closed self-test coverage")
val (out, err, code) = _run("sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --strict")
expect(code).to_equal(0)

step("Strict mode reports a complete wrapper coverage pass")
expect(out).to_contain("nvme_baremetal_wrapper_coverage_status=pass")
expect(out).to_contain("nvme_baremetal_wrapper_coverage_blockers=none")
expect(out).to_contain("STATUS: PASS nvme-baremetal-wrapper-coverage status=pass blockers=none")
_expect_no_fail_marker(out, "strict wrapper coverage audit")
```

</details>

#### self-tests fake wrapper coverage failure modes

- self-tests fake wrapper coverage failure modes
- Run the wrapper coverage fake-fixture self-test
   - Expected: code equals `0`
- The self-test proves fake missing RV64 and RV32 coverage fail closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("self-tests fake wrapper coverage failure modes")
step("Run the wrapper coverage fake-fixture self-test")
val (out, err, code) = _run("sh scripts/check/check-nvme-baremetal-wrapper-coverage.shs --self-test")
expect(code).to_equal(0)

step("The self-test proves fake missing RV64 and RV32 coverage fail closed")
expect(out).to_contain("STATUS: PASS nvme-baremetal-wrapper-coverage self-test")
_expect_no_fail_marker(out, "wrapper coverage self-test")
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1973983c992a44d6751d546aae34d68474babb336a7c16a2fc0f3b9c6f73cf57`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1973983c992a44d6751d546aae34d68474babb336a7c16a2fc0f3b9c6f73cf57`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1973983c992a44d6751d546aae34d68474babb336a7c16a2fc0f3b9c6f73cf57`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/nvme_firmware/nvme_baremetal_wrapper_coverage_spec.spl
mirror: doc/06_spec/03_system/app/nvme_firmware/nvme_baremetal_wrapper_coverage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/nvme_firmware/nvme_baremetal_wrapper_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/nvme_firmware/nvme_baremetal_wrapper_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/nvme_firmware/nvme_baremetal_wrapper_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/nvme_firmware/nvme_baremetal_wrapper_coverage_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports RV32 and RV64 wrapper coverage in default mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/nvme_firmware/nvme_baremetal_wrapper_coverage_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes strict mode when RV32 and RV64 wrapper coverage exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/nvme_firmware/nvme_baremetal_wrapper_coverage_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'self-tests fake wrapper coverage failure modes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
