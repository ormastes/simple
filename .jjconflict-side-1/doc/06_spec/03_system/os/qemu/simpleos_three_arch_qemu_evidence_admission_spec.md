# simpleos_three_arch_qemu_evidence_admission_spec

> Three-architecture SimpleOS QEMU evidence admission contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_three_arch_qemu_evidence_admission_spec

Three-architecture SimpleOS QEMU evidence admission contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Three-architecture SimpleOS QEMU evidence admission contract.

Evidence class: source-contract. These scenarios execute the production
admission adapter without QEMU. They do not claim a live guest PASS; x86_64,
AArch64, and RV64GC remain blocked until retained bundles pass the adapter.

## Scenarios

### REQ-ARCH-EVIDENCE-001: fail-closed three-architecture QEMU evidence

#### should reject an empty evidence record and retain the no-symlink boundary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ARCH-EVIDENCE-001
```

</details>

#### should publish the exact supported architecture and firmware profile

- should publish the exact supported architecture and firmware profile
- Read the closed admission profile from the production adapter
   - Expected: status equals `0`
   - Expected: stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should publish the exact supported architecture and firmware profile")
step("Read the closed admission profile from the production adapter")
val (stdout, stderr, status) = process_run("sh", [CHECKER, "--schema"])
expect(status).to_equal(0)
expect(stderr).to_equal("")
expect(stdout).to_contain("guests=x86_64,arm64,riscv64")
expect(stdout).to_contain("firmware=x86_64:uefi-pflash,arm64:uefi-pflash,riscv64:opensbi-bios")
expect(stdout).to_contain("promotion=blocked-until-signed-campaign-and-no-follow-fd-hash-owner")
```

</details>

#### should require retained compiler, image, program, firmware, argv, and log artifacts

- should require retained compiler, image, program, firmware, argv, and log artifacts
- Inspect the production adapter's immutable artifact contract
   - Expected: status equals `0`
   - Expected: stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require retained compiler, image, program, firmware, argv, and log artifacts")
step("Inspect the production adapter's immutable artifact contract")
val (stdout, stderr, status) = process_run("sh", [CHECKER, "--schema"])
expect(status).to_equal(0)
expect(stderr).to_equal("")
expect(stdout).to_contain("compiler=retained-stage4-pure-simple-source-bound-no-symlink")
expect(stdout).to_contain("artifacts=compiler,compiler-admission,kernel,image,program,firmware,uefi-vars-when-applicable,argv,transcript,markers")
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
- `REQ-ARCH-EVIDENCE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `73d09dfeff3a1ac7a660f105d95b5e03b1d81fa0bc48175f180024f70b8d29e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `73d09dfeff3a1ac7a660f105d95b5e03b1d81fa0bc48175f180024f70b8d29e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `73d09dfeff3a1ac7a660f105d95b5e03b1d81fa0bc48175f180024f70b8d29e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl
mirror: doc/06_spec/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=75 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl:22:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should reject an empty evidence record and retain the no-symlink boundary' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl:22:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject an empty evidence record and retain the no-symlink boundary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should publish the exact supported architecture and firmware profile' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should publish the exact supported architecture and firmware profile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require retained compiler, image, program, firmware, argv, and log artifacts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/simpleos_three_arch_qemu_evidence_admission_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require retained compiler, image, program, firmware, argv, and log artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
