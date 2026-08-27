# SOSIX positioned filesystem matrix acceptance

> This specification admits FAT32, NVFS, and DBFS positioned owners and the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SOSIX positioned filesystem matrix acceptance

This specification admits FAT32, NVFS, and DBFS positioned owners and the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Plan | `doc/03_plan/sys_test/sosix_qemu_remaining_owners.md` |
| Source | `test/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This specification admits FAT32, NVFS, and DBFS positioned owners and the
SimpleOS NVFS live guest only through a source-matched Stage-4 pure-Simple
runtime, exact runtime receipt, linked kernel, and immutable image manifest.
Source checks or missing prerequisites never become live-guest PASS evidence.

**Guide:** `doc/07_guide/platform/simpleos/sosix_qemu_shared_settings.md`

## Scenarios

### SOSIX positioned filesystem matrix

#### should validate source contracts and reject an unqualified guest environment

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should validate source contracts and reject an unqualified guest environment
- Validate positioned filesystem source contracts
   - Expected: source.exit_code equals `0`
   - Expected: source.stderr equals ``
- Reject an unqualified live-guest environment
   - Expected: rejected.stdout equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should validate source contracts and reject an unqualified guest environment")
step("Validate positioned filesystem source contracts")
val source = run_positioned_filesystem_gate(["--self-test"])
expect(source.exit_code).to_equal(0)
expect(source.stderr).to_equal("")
expect(source.stdout).to_contain("sosix_positioned_filesystem_source_contract=pass")
expect(source.stdout).to_contain("simpleos_nvfs_image_manifest_sabotage_rejection=pass")
expect(source.stdout).to_contain("simpleos_nvfs_kernel_build_receipt_sabotage_rejection=pass")
step("Reject an unqualified live-guest environment")
val rejected = run_nvfs_qemu_gate(["--admit", "", "", "", "", "", ""])
expect(rejected.exit_code).to_be_greater_than(0)
expect(rejected.stdout).to_equal("")
expect(rejected.stderr).to_contain("stage4-admission-failed")
```

</details>

#### should exercise qualified filesystem owners and the NVFS live guest

- should exercise qualified filesystem owners and the NVFS live guest
   - Artifact capture: after_step
- Bind the admitted pure-Simple runtime
   - Artifact capture: after_step
- Exercise NVFS and DBFS positioned owners
   - Artifact capture: after_step
- Boot the NVFS-backed SimpleOS guest
   - Artifact capture: after_step
- Verify cursor-independent guest I/O
   - Artifact capture: after_step
- Retain filesystem matrix evidence
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should exercise qualified filesystem owners and the NVFS live guest")
step("Bind the admitted pure-Simple runtime")
val environment = qualified_positioned_environment()
step("Exercise NVFS and DBFS positioned owners")
val evidence = run_positioned_filesystem_gate(["--admit"] + environment)
expect_positioned_backend_evidence(evidence)
step("Boot the NVFS-backed SimpleOS guest")
expect_nvfs_live_guest_evidence(evidence)
step("Verify cursor-independent guest I/O")
expect(evidence.stdout).to_contain("simpleos_nvfs_positioned_live_guest=pass")
step("Retain filesystem matrix evidence")
expect(evidence.stdout).to_contain("sosix_positioned_filesystem_matrix_acceptance=pass")
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


## Related Documentation

- **Plan:** ``doc/03_plan/sys_test/sosix_qemu_remaining_owners.md``


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8ff405c4777033b7ef8fa4f6822ec83fbc9fe202ccbd43873dfc6fcb69ced9cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ff405c4777033b7ef8fa4f6822ec83fbc9fe202ccbd43873dfc6fcb69ced9cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ff405c4777033b7ef8fa4f6822ec83fbc9fe202ccbd43873dfc6fcb69ced9cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.spl
mirror: doc/06_spec/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.spl:100:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate source contracts and reject an unqualified guest environment' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should validate source contracts and reject an unqualified guest environment' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/sosix_positioned_filesystem_matrix_spec.spl:121:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exercise qualified filesystem owners and the NVFS live guest' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
