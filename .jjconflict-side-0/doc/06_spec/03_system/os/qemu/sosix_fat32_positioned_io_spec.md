# SOSIX FAT32 positioned-I/O acceptance

> This fail-closed system specification admits the concrete FAT32 positioned

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SOSIX FAT32 positioned-I/O acceptance

This fail-closed system specification admits the concrete FAT32 positioned

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Plan | `doc/03_plan/sys_test/sosix_qemu_remaining_owners.md` |
| Source | `test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This fail-closed system specification admits the concrete FAT32 positioned
backend only when a receipt-bound pure-Simple runtime executes all focused
owners and a linked x86_64 kernel contains the strong syscall 134/135 leaves.
It never treats source inspection, the Rust seed, or an unavailable registry
environment as runtime or QEMU PASS evidence.

**Guide:** `doc/07_guide/platform/simpleos/sosix_qemu_shared_settings.md`

## Scenarios

### SOSIX FAT32 positioned I/O

#### should keep the source and rejection contracts fail closed

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should keep the source and rejection contracts fail closed
- Validate the concrete positioned owner
   - Expected: source.exit_code equals `0`
   - Expected: source.stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep the source and rejection contracts fail closed")
step("Validate the concrete positioned owner")
val source = run_positioned_gate(["--self-test"])
expect(source.exit_code).to_equal(0)
expect(source.stderr).to_equal("")
expect(source.stdout).to_contain(
    "sosix_fat32_positioned_source_contract=pass")
expect(source.stdout).to_contain(
    "sosix_fat32_positioned_runtime_rejection=pass")
expect(source.stdout).to_contain(
    "sosix_fat32_positioned_self_test=pass")
```

</details>

#### should reject absent runtime receipts and linked artifacts before testing

- should reject absent runtime receipts and linked artifacts before testing
- Reject an unqualified positioned environment
   - Expected: rejected.stdout equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject absent runtime receipts and linked artifacts before testing")
step("Reject an unqualified positioned environment")
val rejected = run_positioned_gate(["--admit", "", "", ""])
expect(rejected.exit_code).to_be_greater_than(0)
expect(rejected.stdout).to_equal("")
expect(rejected.stderr).to_contain("missing-runtime:")
expect(rejected.stderr).to_contain("runtime-admission-failed")
```

</details>

#### should admit one qualified runtime linked route and focused owner suite

- should admit one qualified runtime linked route and focused owner suite
- Bind the admitted runtime
   - Expected: admitted.exit_code equals `0`
   - Expected: admitted.stderr equals ``
- Exercise positioned filesystem owners
- Retain fail-closed evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should admit one qualified runtime linked route and focused owner suite")
step("Bind the admitted runtime")
val runtime = env_get("SOSIX_POSITIONED_SIMPLE_RUNTIME")
val receipt = env_get("SOSIX_POSITIONED_RUNTIME_RECEIPT")
val kernel = env_get("SOSIX_POSITIONED_KERNEL_ELF")
val admitted = run_positioned_gate(
    ["--admit", runtime, receipt, kernel])
expect(admitted.exit_code).to_equal(0)
expect(admitted.stderr).to_equal("")
expect(admitted.stdout).to_contain(
    "sosix_fat32_positioned_linked_route=pass")
step("Exercise positioned filesystem owners")
expect(admitted.stdout).to_contain(
    "sosix_fat32_positioned_primitives=pass")
expect(admitted.stdout).to_contain(
    "sosix_fat32_file_object_owner=pass")
expect(admitted.stdout).to_contain(
    "sosix_fat32_positioned_backend=pass")
step("Retain fail-closed evidence")
expect(admitted.stdout).to_contain(
    "sosix_fat32_positioned_runtime_sha256=")
expect(admitted.stdout).to_contain(
    "sosix_fat32_positioned_acceptance=pass")
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

- **Plan:** ``doc/03_plan/sys_test/sosix_qemu_remaining_owners.md``


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3db98630866f802f53005c77c7bd861ad81c7d68985f5591c2c919a7224ddf02`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3db98630866f802f53005c77c7bd861ad81c7d68985f5591c2c919a7224ddf02`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3db98630866f802f53005c77c7bd861ad81c7d68985f5591c2c919a7224ddf02`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl
mirror: doc/06_spec/03_system/os/qemu/sosix_fat32_positioned_io_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/sosix_fat32_positioned_io_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/sosix_fat32_positioned_io_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the source and rejection contracts fail closed' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep the source and rejection contracts fail closed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject absent runtime receipts and linked artifacts before testing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject absent runtime receipts and linked artifacts before testing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should admit one qualified runtime linked route and focused owner suite' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/sosix_fat32_positioned_io_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should admit one qualified runtime linked route and focused owner suite' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
