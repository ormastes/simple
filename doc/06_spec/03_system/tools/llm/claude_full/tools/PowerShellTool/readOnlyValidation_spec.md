# Claude Full PowerShell Read-Only Validation Slice

> Focused coverage for read-only decision surfaces from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full PowerShell Read-Only Validation Slice

Focused coverage for read-only decision surfaces from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/PowerShellTool/readOnlyValidation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for read-only decision surfaces from
tools/PowerShellTool/readOnlyValidation.ts.

## Scenarios

### Claude full powershell read only validation parity

#### should model sync security concerns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model sync security concerns
- Check security concerns
   - Expected: hasSyncSecurityConcernsRoute("Get-Content file.txt") is false
   - Expected: hasSyncSecurityConcernsRoute("Write-Output $(Get-Date)") is true
   - Expected: hasSyncSecurityConcernsRoute("Invoke-Item @splat") is true
   - Expected: hasSyncSecurityConcernsRoute("[Type]::Method()") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model sync security concerns")
step("Check security concerns")
expect(hasSyncSecurityConcernsRoute("Get-Content file.txt")).to_equal(false)
expect(hasSyncSecurityConcernsRoute("Write-Output $(Get-Date)")).to_equal(true)
expect(hasSyncSecurityConcernsRoute("Invoke-Item @splat")).to_equal(true)
expect(hasSyncSecurityConcernsRoute("[Type]::Method()")).to_equal(true)
```

</details>

#### should model read only decisions

- should model read only decisions
- Check read-only classification
   - Expected: isReadOnlyCommandRoute("") is false
   - Expected: isReadOnlyCommandRoute("Get-Content file.txt") is true
   - Expected: isReadOnlyCommandRoute("Get-Content file.txt > out.txt") is false
   - Expected: isReadOnlyCommandRoute("Set-Location /tmp; Get-Content x") is false
   - Expected: isReadOnlyCommandRoute("Get-Content x | Select-Object") is true
   - Expected: isReadOnlyCommandRoute("Write-Output $(Get-Date)") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model read only decisions")
step("Check read-only classification")
expect(isReadOnlyCommandRoute("")).to_equal(false)
expect(isReadOnlyCommandRoute("Get-Content file.txt")).to_equal(true)
expect(isReadOnlyCommandRoute("Get-Content file.txt > out.txt")).to_equal(false)
expect(isReadOnlyCommandRoute("Set-Location /tmp; Get-Content x")).to_equal(false)
expect(isReadOnlyCommandRoute("Get-Content x | Select-Object")).to_equal(true)
expect(isReadOnlyCommandRoute("Write-Output $(Get-Date)")).to_equal(false)
```

</details>

#### should model representative allowlist routes

- should model representative allowlist routes
- Check allowlist
   - Expected: isAllowlistedCommandRoute("Get-ChildItem .") is true
   - Expected: isAllowlistedCommandRoute("Remove-Item file") is false
   - Expected: powershellReadOnlyValidationSourceLinesModeled() equals `1823`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model representative allowlist routes")
step("Check allowlist")
expect(isAllowlistedCommandRoute("Get-ChildItem .")).to_equal(true)
expect(isAllowlistedCommandRoute("Remove-Item file")).to_equal(false)
expect(powershellReadOnlyValidationSourceLinesModeled()).to_equal(1823)
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

- Canonical SPipe generation for source `5b30b6c7e730b5b6513b36c83f7e41d6f2242f1ce96340ac8634f59dd4241f25`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5b30b6c7e730b5b6513b36c83f7e41d6f2242f1ce96340ac8634f59dd4241f25`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5b30b6c7e730b5b6513b36c83f7e41d6f2242f1ce96340ac8634f59dd4241f25`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/tools/PowerShellTool/readOnlyValidation_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/tools/PowerShellTool/readOnlyValidation_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/tools/PowerShellTool/readOnlyValidation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/tools/PowerShellTool/readOnlyValidation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/readOnlyValidation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/readOnlyValidation_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model sync security concerns' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/readOnlyValidation_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model sync security concerns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/readOnlyValidation_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model read only decisions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/readOnlyValidation_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model read only decisions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/readOnlyValidation_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model representative allowlist routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/readOnlyValidation_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model representative allowlist routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
