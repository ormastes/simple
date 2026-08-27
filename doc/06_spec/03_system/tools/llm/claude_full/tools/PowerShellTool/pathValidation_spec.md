# Claude Full PowerShell Path Validation Slice

> Focused coverage for public path-constraint and dangerous-removal routing from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full PowerShell Path Validation Slice

Focused coverage for public path-constraint and dangerous-removal routing from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/PowerShellTool/pathValidation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for public path-constraint and dangerous-removal routing from
tools/PowerShellTool/pathValidation.ts.

## Scenarios

### Claude full powershell path validation parity

#### should model passthrough read path routes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model passthrough read path routes
- Check passthrough routes
   - Expected: checkPathConstraintsRoute("Get-Content ./file.txt", false, false, false, false, false, false) equals `passthrough`
   - Expected: checkPathConstraintsRoute("Get-Content ./file.txt", true, true, false, false, false, false) equals `passthrough`
   - Expected: checkPathConstraintsRoute("Invoke-WebRequest https://example.test", true, false, false, false, false, false) equals `passthrough`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model passthrough read path routes")
step("Check passthrough routes")
expect(checkPathConstraintsRoute("Get-Content ./file.txt", false, false, false, false, false, false)).to_equal("passthrough")
expect(checkPathConstraintsRoute("Get-Content ./file.txt", true, true, false, false, false, false)).to_equal("passthrough")
expect(checkPathConstraintsRoute("Invoke-WebRequest https://example.test", true, false, false, false, false, false)).to_equal("passthrough")
```

</details>

#### should model deny routes

- should model deny routes
- Check deny routes
   - Expected: isDangerousRemovalRawPathRoute("Remove-Item /") is true
   - Expected: dangerousRemovalDenyRoute("rm /etc") equals `deny dangerous removal`
   - Expected: checkPathConstraintsRoute("Remove-Item /", true, false, false, false, false, false) equals `deny dangerous removal`
   - Expected: checkPathConstraintsRoute("rm /etc", true, false, false, false, false, false) equals `deny dangerous removal`
   - Expected: checkPathConstraintsRoute("Get-Content /secret", true, false, true, false, false, false) equals `deny blocked path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model deny routes")
step("Check deny routes")
expect(isDangerousRemovalRawPathRoute("Remove-Item /")).to_equal(true)
expect(dangerousRemovalDenyRoute("rm /etc")).to_equal("deny dangerous removal")
expect(checkPathConstraintsRoute("Remove-Item /", true, false, false, false, false, false)).to_equal("deny dangerous removal")
expect(checkPathConstraintsRoute("rm /etc", true, false, false, false, false, false)).to_equal("deny dangerous removal")
expect(checkPathConstraintsRoute("Get-Content /secret", true, false, true, false, false, false)).to_equal("deny blocked path")
```

</details>

#### should model ask routes

- should model ask routes
- Check ask routes
   - Expected: checkPathConstraintsRoute("Get-Content /outside", true, false, false, false, false, false) equals `ask blocked path`
   - Expected: checkPathConstraintsRoute("Set-Location /tmp; Get-Content x", true, false, false, true, false, false) equals `ask cwd changing command`
   - Expected: checkPathConstraintsRoute("'x' | Get-Content", true, false, false, false, true, false) equals `ask pipeline path`
   - Expected: checkPathConstraintsRoute("Get-Content $path", true, false, false, false, false, true) equals `ask complex path`
   - Expected: checkPathConstraintsRoute("Set-Content", true, false, false, false, false, false) equals `ask write target`
   - Expected: powershellPathValidationSourceLinesModeled() equals `2049`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model ask routes")
step("Check ask routes")
expect(checkPathConstraintsRoute("Get-Content /outside", true, false, false, false, false, false)).to_equal("ask blocked path")
expect(checkPathConstraintsRoute("Set-Location /tmp; Get-Content x", true, false, false, true, false, false)).to_equal("ask cwd changing command")
expect(checkPathConstraintsRoute("'x' | Get-Content", true, false, false, false, true, false)).to_equal("ask pipeline path")
expect(checkPathConstraintsRoute("Get-Content $path", true, false, false, false, false, true)).to_equal("ask complex path")
expect(checkPathConstraintsRoute("Set-Content", true, false, false, false, false, false)).to_equal("ask write target")
expect(powershellPathValidationSourceLinesModeled()).to_equal(2049)
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

- Canonical SPipe generation for source `137e77b240e2634f11baade8d4fa871230a853a9346e7e9c516f9f4246586909`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `137e77b240e2634f11baade8d4fa871230a853a9346e7e9c516f9f4246586909`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `137e77b240e2634f11baade8d4fa871230a853a9346e7e9c516f9f4246586909`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/tools/PowerShellTool/pathValidation_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/tools/PowerShellTool/pathValidation_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/tools/PowerShellTool/pathValidation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/tools/PowerShellTool/pathValidation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/pathValidation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/pathValidation_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model passthrough read path routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/pathValidation_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model passthrough read path routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/pathValidation_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model deny routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/pathValidation_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model deny routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/pathValidation_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model ask routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/pathValidation_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model ask routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
