# Claude Full PowerShell Parser Slice

> Focused coverage for parse envelope and transform routes from

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full PowerShell Parser Slice

Focused coverage for parse envelope and transform routes from

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/powershell/parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Focused coverage for parse envelope and transform routes from
utils/powershell/parser.ts.

## Scenarios

### Claude full powershell parser parity

#### should model invalid parse result routes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should model invalid parse result routes
- Check invalid parse routes
   - Expected: parsePowerShellCommandRoute("empty") equals `invalid NoInput`
   - Expected: parsePowerShellCommandRoute("too_long") equals `invalid CommandTooLong`
   - Expected: parsePowerShellCommandRoute("missing_pwsh") equals `invalid NoPowerShell`
   - Expected: parsePowerShellCommandRoute("spawn_failure") equals `invalid PwshSpawnError`
   - Expected: parsePowerShellCommandRoute("timeout") equals `invalid PwshTimeout`
   - Expected: parsePowerShellCommandRoute("nonzero_exit") equals `invalid PwshError`
   - Expected: parsePowerShellCommandRoute("empty_stdout") equals `invalid EmptyOutput`
   - Expected: parsePowerShellCommandRoute("invalid_json") equals `invalid InvalidJson`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model invalid parse result routes")
step("Check invalid parse routes")
expect(parsePowerShellCommandRoute("empty")).to_equal("invalid NoInput")
expect(parsePowerShellCommandRoute("too_long")).to_equal("invalid CommandTooLong")
expect(parsePowerShellCommandRoute("missing_pwsh")).to_equal("invalid NoPowerShell")
expect(parsePowerShellCommandRoute("spawn_failure")).to_equal("invalid PwshSpawnError")
expect(parsePowerShellCommandRoute("timeout")).to_equal("invalid PwshTimeout")
expect(parsePowerShellCommandRoute("nonzero_exit")).to_equal("invalid PwshError")
expect(parsePowerShellCommandRoute("empty_stdout")).to_equal("invalid EmptyOutput")
expect(parsePowerShellCommandRoute("invalid_json")).to_equal("invalid InvalidJson")
```

</details>

#### should model valid raw output and mapping routes

- should model valid raw output and mapping routes
- Check transform routes
   - Expected: parsePowerShellCommandRoute("valid") equals `valid parsed command`
   - Expected: transformRawOutputRoute(true, true, true, true) equals `parsed envelope complete`
   - Expected: transformRawOutputRoute(false, false, false, false) equals `invalid raw output`
   - Expected: mapStatementTypeRoute("Pipeline") equals `pipeline`
   - Expected: mapStatementTypeRoute("Other") equals `unknown`
   - Expected: mapElementTypeRoute("CommandName") equals `command_name`
   - Expected: mapElementTypeRoute("Other") equals `unknown`
   - Expected: transformRedirectionRoute("null", "") equals `null redirection`
   - Expected: transformRedirectionRoute("file", "out.txt") equals `file redirection`
   - Expected: powershellParserSourceLinesModeled() equals `1805`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model valid raw output and mapping routes")
step("Check transform routes")
expect(parsePowerShellCommandRoute("valid")).to_equal("valid parsed command")
expect(transformRawOutputRoute(true, true, true, true)).to_equal("parsed envelope complete")
expect(transformRawOutputRoute(false, false, false, false)).to_equal("invalid raw output")
expect(mapStatementTypeRoute("Pipeline")).to_equal("pipeline")
expect(mapStatementTypeRoute("Other")).to_equal("unknown")
expect(mapElementTypeRoute("CommandName")).to_equal("command_name")
expect(mapElementTypeRoute("Other")).to_equal("unknown")
expect(transformRedirectionRoute("null", "")).to_equal("null redirection")
expect(transformRedirectionRoute("file", "out.txt")).to_equal("file redirection")
expect(powershellParserSourceLinesModeled()).to_equal(1805)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `56cb5434ff74c3af3394f656c08a3e0c540ed7d690995d214b2db9c86cc458ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `56cb5434ff74c3af3394f656c08a3e0c540ed7d690995d214b2db9c86cc458ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `56cb5434ff74c3af3394f656c08a3e0c540ed7d690995d214b2db9c86cc458ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/utils/powershell/parser_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/powershell/parser_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/powershell/parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/powershell/parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/powershell/parser_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/powershell/parser_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model invalid parse result routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/powershell/parser_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model invalid parse result routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/powershell/parser_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model valid raw output and mapping routes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/powershell/parser_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model valid raw output and mapping routes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
