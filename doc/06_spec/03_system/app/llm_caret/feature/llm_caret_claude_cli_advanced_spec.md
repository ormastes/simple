# LLM Caret Advanced Claude CLI Forwarding

> Verifies the llm caret claude cli advanced behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Advanced Claude CLI Forwarding

Verifies the llm caret claude cli advanced behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Plan | doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the llm caret claude cli advanced behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### LLM Caret advanced Claude CLI forwarding

### REQ-LLM-CARET-FULL-003: advanced Claude provider request

#### should forward the advanced request through the production Claude sender

- Verify: should forward the advanced request through the production Claude sender
- Prepare offline Claude CLI fixture
- Send advanced provider request
- Check forwarded response and status
   - Expected: response.content equals `advanced-ok`
   - Expected: response.model equals `sonnet`
   - Expected: response.session_id equals `advanced-session`
   - Expected: response.stop_reason equals `end_turn`
   - Expected: response.error equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-FULL-003
step("Verify: should forward the advanced request through the production Claude sender")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Prepare offline Claude CLI fixture")
expect(file_exists(MOCK_CLAUDE)).to_be(true)

step("Send advanced provider request")
val response = claude_cli_send(
    MOCK_CLAUDE, "fixture-advanced", "sonnet", "Be concise",
    "advanced-resume", 3, 0, "{\"type\":\"object\"}",
    ["Read", "Write"], ["--fixture-extra"]
)

step("Check forwarded response and status")
expect(response.is_error).to_be(false)
expect(response.content).to_equal("advanced-ok")
expect(response.model).to_equal("sonnet")
expect(response.session_id).to_equal("advanced-session")
expect(response.stop_reason).to_equal("end_turn")
expect(response.error).to_equal("")
expect(response.raw).to_contain("advanced-ok")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `38d6b1fa87cf3ba23baedb3773d70921a5cf5d8aec5153a7cc6825f291a4c982`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38d6b1fa87cf3ba23baedb3773d70921a5cf5d8aec5153a7cc6825f291a4c982`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38d6b1fa87cf3ba23baedb3773d70921a5cf5d8aec5153a7cc6825f291a4c982`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should forward the advanced request through the production Claude sender' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
