# Claude Full PowerShell Permissions Slice

> Focused Simple coverage for PowerShell permission rule-core behavior from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full PowerShell Permissions Slice

Focused Simple coverage for PowerShell permission rule-core behavior from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/tools/PowerShellTool/powershellPermissions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused Simple coverage for PowerShell permission rule-core behavior from
tools/PowerShellTool/powershellPermissions.ts.

## Scenarios

### Claude full powershell permissions parity

#### should model exact permission decisions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model exact permission decisions
- Check exact decisions
   - Expected: powershellToolCheckExactMatchPermissionRoute("Get-Content x", true, true, true) equals `deny`
   - Expected: powershellToolCheckExactMatchPermissionRoute("Get-Content x", false, true, true) equals `ask PowerShell command requires permission`
   - Expected: powershellToolCheckExactMatchPermissionRoute("Get-Content x", false, false, true) equals `allow updatedInput Get-Content x`
   - Expected: powershellToolCheckExactMatchPermissionRoute("Get-Content x", false, false, false) equals `passthrough allow exact Get-Content x`
   - Expected: suggestionForExactCommandRoute("Get-Content *") equals `none`
   - Expected: suggestionForExactCommandRoute("Get-Content x\nGet-Content y") equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model exact permission decisions")
step("Check exact decisions")
expect(powershellToolCheckExactMatchPermissionRoute("Get-Content x", true, true, true)).to_equal("deny")
expect(powershellToolCheckExactMatchPermissionRoute("Get-Content x", false, true, true)).to_equal("ask PowerShell command requires permission")
expect(powershellToolCheckExactMatchPermissionRoute("Get-Content x", false, false, true)).to_equal("allow updatedInput Get-Content x")
expect(powershellToolCheckExactMatchPermissionRoute("Get-Content x", false, false, false)).to_equal("passthrough allow exact Get-Content x")
expect(suggestionForExactCommandRoute("Get-Content *")).to_equal("none")
expect(suggestionForExactCommandRoute("Get-Content x\nGet-Content y")).to_equal("none")
```

</details>

#### should model normalization alias and module rules

- should model normalization alias and module rules
- Check matching rules
   - Expected: normalizePowerShellCommandRoute("Get-Content\tX") equals `get-content x`
   - Expected: powershellRuleMatchesRoute("Remove-Item /tmp/x", "rm /tmp/x", "exact", "deny") is true
   - Expected: powershellRuleMatchesRoute("Microsoft.PowerShell.Management\\Remove-Item /tmp/x", "rm /tmp/x", "exact", "deny") is true
   - Expected: powershellRuleMatchesRoute("Microsoft.PowerShell.Management\\Remove-Item /tmp/x", "rm /tmp/x", "exact", "allow") is false
   - Expected: powershellRuleMatchesRoute("Get-Content", "get-content x", "prefix", "allow") is true
   - Expected: powershellRuleMatchesRoute("Get-Content", "get-content x", "exact", "allow") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model normalization alias and module rules")
step("Check matching rules")
expect(normalizePowerShellCommandRoute("Get-Content\tX")).to_equal("get-content x")
expect(powershellRuleMatchesRoute("Remove-Item /tmp/x", "rm /tmp/x", "exact", "deny")).to_equal(true)
expect(powershellRuleMatchesRoute("Microsoft.PowerShell.Management\\Remove-Item /tmp/x", "rm /tmp/x", "exact", "deny")).to_equal(true)
expect(powershellRuleMatchesRoute("Microsoft.PowerShell.Management\\Remove-Item /tmp/x", "rm /tmp/x", "exact", "allow")).to_equal(false)
expect(powershellRuleMatchesRoute("Get-Content", "get-content x", "prefix", "allow")).to_equal(true)
expect(powershellRuleMatchesRoute("Get-Content", "get-content x", "exact", "allow")).to_equal(false)
```

</details>

#### should model aggregate permission precedence

- should model aggregate permission precedence
- Check aggregate decisions
   - Expected: powershellToolCheckPermissionRoute("Get-Content x", true, true, true) equals `deny`
   - Expected: powershellToolCheckPermissionRoute("Get-Content x", false, true, true) equals `ask PowerShell command requires permission`
   - Expected: powershellToolCheckPermissionRoute("Get-Content x", false, false, true) equals `allow updatedInput Get-Content x`
   - Expected: powershellToolCheckPermissionRoute("Get-Content x", false, false, false) equals `passthrough approval prompt`
   - Expected: powershellPermissionRuleRoute("allow", "Get-Content", "prefix") equals `allow:prefix:Get-Content`
   - Expected: powershellPermissionsSourceLinesModeled() equals `1648`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model aggregate permission precedence")
step("Check aggregate decisions")
expect(powershellToolCheckPermissionRoute("Get-Content x", true, true, true)).to_equal("deny")
expect(powershellToolCheckPermissionRoute("Get-Content x", false, true, true)).to_equal("ask PowerShell command requires permission")
expect(powershellToolCheckPermissionRoute("Get-Content x", false, false, true)).to_equal("allow updatedInput Get-Content x")
expect(powershellToolCheckPermissionRoute("Get-Content x", false, false, false)).to_equal("passthrough approval prompt")
expect(powershellPermissionRuleRoute("allow", "Get-Content", "prefix")).to_equal("allow:prefix:Get-Content")
expect(powershellPermissionsSourceLinesModeled()).to_equal(1648)
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

- Canonical SPipe generation for source `8187520f09ea1260280bb369a47029ad60176b8bf8fdac5af099983b5e50d685`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8187520f09ea1260280bb369a47029ad60176b8bf8fdac5af099983b5e50d685`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8187520f09ea1260280bb369a47029ad60176b8bf8fdac5af099983b5e50d685`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/tools/PowerShellTool/powershellPermissions_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/tools/PowerShellTool/powershellPermissions_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/tools/PowerShellTool/powershellPermissions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/tools/PowerShellTool/powershellPermissions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/powershellPermissions_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/powershellPermissions_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model exact permission decisions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/powershellPermissions_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model exact permission decisions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/powershellPermissions_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model normalization alias and module rules' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/powershellPermissions_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model normalization alias and module rules' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/powershellPermissions_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model aggregate permission precedence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/tools/PowerShellTool/powershellPermissions_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model aggregate permission precedence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
