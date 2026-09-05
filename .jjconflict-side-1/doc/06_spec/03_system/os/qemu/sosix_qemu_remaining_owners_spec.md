# SOSIX QEMU remaining-owner handoff

> This executable manual verifies the shared fail-closed owner gate and the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SOSIX QEMU remaining-owner handoff

This executable manual verifies the shared fail-closed owner gate and the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Plan | `doc/03_plan/agent_tasks/sosix_parallel_qemu_refactor.md` |
| Source | `test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This executable manual verifies the shared fail-closed owner gate and the
typed handoff oracle for every one of the 24 host/guest rows. A BLOCKED or
POSTPONED oracle is success for this handoff spec only: it proves that the row
was retained and cannot be promoted. It is never live QEMU PASS evidence.

**Tracking:** `doc/08_tracking/bug/sosix_qemu_matrix_remaining_owners_2026-08-14.md`

## Scenarios

### SOSIX QEMU remaining-owner handoff

<details>
<summary>Advanced: should enforce the shared matrix ownership boundaries behaviorally</summary>

#### should enforce the shared matrix ownership boundaries behaviorally

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should enforce the shared matrix ownership boundaries behaviorally
- Validate matrix promotion
   - Expected: evidence.exit_code equals `0`
   - Expected: evidence.stderr equals ``
- Reject mutable source aliasing
- Bind the admitted runtime
   - Expected: truncated.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should enforce the shared matrix ownership boundaries behaviorally")
step("Validate matrix promotion")
val evidence = run_check("sh scripts/check/check-sosix-qemu-shared-owners.shs --self-test", 30000)
expect(evidence.exit_code).to_equal(0)
expect(evidence.stderr).to_equal("")
expect(evidence.stdout).to_contain("sosix_qemu_shared_owner_collector_status=pass")
expect(evidence.stdout).to_contain("sosix_qemu_shared_owner_behavioral_fixture_status=pass")
step("Reject mutable source aliasing")
expect(evidence.stdout).to_contain("sosix_qemu_shared_owner_media_alias_status=pass")
expect(evidence.stdout).to_contain("sosix_qemu_shared_owner_media_copy_status=pass")
expect(evidence.stdout).to_contain("sosix_qemu_shared_owner_media_corruption_status=pass")
step("Bind the admitted runtime")
expect(evidence.stdout).to_contain("sosix_qemu_shared_owner_admitted_runtime_status=pass")
val truncated = run_check_with_limit(
    "awk 'BEGIN { for (i = 0; i < 4096; i++) printf \"x\" }'", 5000, 1024)
expect(truncated.exit_code).to_equal(0)
expect(truncated.stdout).to_contain("[output truncated:")
expect(truncated.stdout).to_contain("bytes omitted]")
```

</details>


</details>

#### should retain linked-artifact admission for incomplete Linux lifecycle rows

- should retain linked-artifact admission for incomplete Linux lifecycle rows
- Admit the Linux guest lifecycle
   - Expected: rv64.exit_code equals `0`
   - Expected: x86_source.exit_code equals `0`
   - Expected: arm_source.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain linked-artifact admission for incomplete Linux lifecycle rows")
step("Admit the Linux guest lifecycle")
val rv64 = run_check("sh scripts/check/check-rv64-inline-asm-operand-transport.shs", 30000)
expect(rv64.exit_code).to_equal(0)
val x86_source = run_check("sh scripts/check/check-x86-32-cpl3-lifecycle-contract.shs --self-test", 30000)
expect(x86_source.exit_code).to_equal(0)
expect(x86_source.stdout).to_contain("non-ELF and missing-strong-symbol gates fail closed")
val x86_link = run_check("sh scripts/check/check-x86-32-cpl3-lifecycle-contract.shs --admit build/os/__missing_sosix_x86_32_lifecycle.elf", 30000)
expect(x86_link.exit_code).to_be_greater_than(0)
expect(x86_link.stdout + x86_link.stderr).to_contain("linked kernel missing")
val arm_source = run_check("sh scripts/check/check-arm32-user-lifecycle-contract.shs --self-test", 30000)
expect(arm_source.exit_code).to_equal(0)
expect(arm_source.stdout).to_contain("non-ELF and missing-strong-symbol gates fail closed")
val arm_link = run_check("sh scripts/check/check-arm32-user-lifecycle-contract.shs --admit build/os/__missing_sosix_arm32_lifecycle.elf", 30000)
expect(arm_link.exit_code).to_be_greater_than(0)
expect(arm_link.stdout + arm_link.stderr).to_contain("linked kernel missing")
val tracking = file_read_text("doc/08_tracking/bug/sosix_qemu_matrix_remaining_owners_2026-08-14.md")
expect(tracking).to_contain("RV64 compiler owner")
```

</details>

#### should retain a typed fail-closed oracle for all 24 acceptance rows

- should retain a typed fail-closed oracle for all 24 acceptance rows
- Record unavailable native hosts
   - Expected: rows.len() equals `24`
   - Expected: pass_count equals `3`
   - Expected: blocked_count equals `15`
   - Expected: postponed_count equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain a typed fail-closed oracle for all 24 acceptance rows")
step("Record unavailable native hosts")
val plan = file_read_text("doc/03_plan/agent_tasks/sosix_parallel_qemu_refactor.md")
val rows = retained_rows()
expect(rows.len()).to_equal(24)
var pass_count = 0
var blocked_count = 0
var postponed_count = 0
for row in rows:
    expect(plan).to_contain("| `" + row.acceptance_id + "` | " + row.expected_state + " |")
    if row.expected_state == "PASS": pass_count = pass_count + 1
    if row.expected_state == "BLOCKED": blocked_count = blocked_count + 1
    if row.expected_state == "POSTPONED": postponed_count = postponed_count + 1
expect(pass_count).to_equal(3)
expect(blocked_count).to_equal(15)
expect(postponed_count).to_equal(6)
```

</details>

#### should retain exact owners and unblock conditions for incomplete work

- should retain exact owners and unblock conditions for incomplete work
- Retain the implementation handoff


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain exact owners and unblock conditions for incomplete work")
step("Retain the implementation handoff")
val tracking = file_read_text("doc/08_tracking/bug/sosix_qemu_matrix_remaining_owners_2026-08-14.md")
expect(tracking).to_contain("RV64 compiler owner")
expect(tracking).to_contain("x86_32 kernel owner")
expect(tracking).to_contain("ARM32 kernel owner")
expect(tracking).to_contain("Windows operator")
expect(tracking).to_contain("FreeBSD operator")
expect(tracking).to_contain("macOS operator")
expect(tracking).to_contain("System-test/docgen owner")
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


## Related Documentation

- **Plan:** ``doc/03_plan/agent_tasks/sosix_parallel_qemu_refactor.md``


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9bbd6898a7a2577329a4af9a28140946a09cadafaf31a82976b4de49be5e652b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9bbd6898a7a2577329a4af9a28140946a09cadafaf31a82976b4de49be5e652b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9bbd6898a7a2577329a4af9a28140946a09cadafaf31a82976b4de49be5e652b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl
mirror: doc/06_spec/03_system/os/qemu/sosix_qemu_remaining_owners_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/sosix_qemu_remaining_owners_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/sosix_qemu_remaining_owners_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should enforce the shared matrix ownership boundaries behaviorally' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should enforce the shared matrix ownership boundaries behaviorally' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain linked-artifact admission for incomplete Linux lifecycle rows' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain linked-artifact admission for incomplete Linux lifecycle rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl:125:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain a typed fail-closed oracle for all 24 acceptance rows' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain a typed fail-closed oracle for all 24 acceptance rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/sosix_qemu_remaining_owners_spec.spl:145:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain exact owners and unblock conditions for incomplete work' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
