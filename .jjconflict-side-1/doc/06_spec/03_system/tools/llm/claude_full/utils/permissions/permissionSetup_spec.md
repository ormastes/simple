# Claude Full Permission Setup Slice

> Focused Simple coverage for dangerous permission predicate helpers from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Permission Setup Slice

Focused Simple coverage for dangerous permission predicate helpers from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/permissions/permissionSetup_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple coverage for dangerous permission predicate helpers from
utils/permissions/permissionSetup.ts.

## Scenarios

### Claude full permission setup parity

#### should model dangerous Bash permissions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model dangerous Bash permissions
- Check Bash danger predicates
   - Expected: isDangerousBashPermissionRoute("Bash", "") is true
   - Expected: isDangerousBashPermissionRoute("Bash", "   ") is true
   - Expected: isDangerousBashPermissionRoute("Bash", "*") is true
   - Expected: isDangerousBashPermissionRoute("Bash", "python") is true
   - Expected: isDangerousBashPermissionRoute("Bash", "python:*") is true
   - Expected: isDangerousBashPermissionRoute("Bash", "python*") is true
   - Expected: isDangerousBashPermissionRoute("Bash", "python *") is true
   - Expected: isDangerousBashPermissionRoute("Bash", "python -c *") is true
   - Expected: isDangerousBashPermissionRoute("Read", "python") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model dangerous Bash permissions")
step("Check Bash danger predicates")
expect(isDangerousBashPermissionRoute("Bash", "")).to_equal(true)
expect(isDangerousBashPermissionRoute("Bash", "   ")).to_equal(true)
expect(isDangerousBashPermissionRoute("Bash", "*")).to_equal(true)
expect(isDangerousBashPermissionRoute("Bash", "python")).to_equal(true)
expect(isDangerousBashPermissionRoute("Bash", "python:*")).to_equal(true)
expect(isDangerousBashPermissionRoute("Bash", "python*")).to_equal(true)
expect(isDangerousBashPermissionRoute("Bash", "python *")).to_equal(true)
expect(isDangerousBashPermissionRoute("Bash", "python -c *")).to_equal(true)
expect(isDangerousBashPermissionRoute("Read", "python")).to_equal(false)
```

</details>

#### should model dangerous PowerShell permissions

- should model dangerous PowerShell permissions
- Check PowerShell danger predicates
   - Expected: isDangerousPowerShellPermissionRoute("PowerShell", "*") is true
   - Expected: isDangerousPowerShellPermissionRoute("PowerShell", "iex:*") is true
   - Expected: isDangerousPowerShellPermissionRoute("PowerShell", "start-process*") is true
   - Expected: isDangerousPowerShellPermissionRoute("PowerShell", "add-type*") is true
   - Expected: isDangerousPowerShellPermissionRoute("Bash", "iex:*") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model dangerous PowerShell permissions")
step("Check PowerShell danger predicates")
expect(isDangerousPowerShellPermissionRoute("PowerShell", "*")).to_equal(true)
expect(isDangerousPowerShellPermissionRoute("PowerShell", "iex:*")).to_equal(true)
expect(isDangerousPowerShellPermissionRoute("PowerShell", "start-process*")).to_equal(true)
expect(isDangerousPowerShellPermissionRoute("PowerShell", "add-type*")).to_equal(true)
expect(isDangerousPowerShellPermissionRoute("Bash", "iex:*")).to_equal(false)
```

</details>

#### should model dangerous Task permissions

- should model dangerous Task permissions
- Check Task danger predicates
   - Expected: isDangerousTaskPermissionRoute("Task", "") is true
   - Expected: isDangerousTaskPermissionRoute("Agent", "") is true
   - Expected: isDangerousTaskPermissionRoute("Read", "") is false
   - Expected: dangerousPermissionInfoRoute("Bash", "python") equals `Bash:python`
   - Expected: permissionSetupSourceLinesModeled() equals `1532`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model dangerous Task permissions")
step("Check Task danger predicates")
expect(isDangerousTaskPermissionRoute("Task", "")).to_equal(true)
expect(isDangerousTaskPermissionRoute("Agent", "")).to_equal(true)
expect(isDangerousTaskPermissionRoute("Read", "")).to_equal(false)
expect(dangerousPermissionInfoRoute("Bash", "python")).to_equal("Bash:python")
expect(permissionSetupSourceLinesModeled()).to_equal(1532)
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

- Canonical SPipe generation for source `0867c63b7d61cc2ed6aa652303b9ed9117bfb9d8154dc8a402179af969d34bc6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0867c63b7d61cc2ed6aa652303b9ed9117bfb9d8154dc8a402179af969d34bc6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0867c63b7d61cc2ed6aa652303b9ed9117bfb9d8154dc8a402179af969d34bc6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/utils/permissions/permissionSetup_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/permissions/permissionSetup_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/permissions/permissionSetup_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/permissions/permissionSetup_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/permissions/permissionSetup_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/permissions/permissionSetup_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model dangerous Bash permissions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/permissions/permissionSetup_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model dangerous Bash permissions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/permissions/permissionSetup_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model dangerous PowerShell permissions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/permissions/permissionSetup_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model dangerous PowerShell permissions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/permissions/permissionSetup_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model dangerous Task permissions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/permissions/permissionSetup_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model dangerous Task permissions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
