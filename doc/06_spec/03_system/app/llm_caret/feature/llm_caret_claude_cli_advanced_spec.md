# LLM Caret Advanced Claude CLI Forwarding

> This deterministic offline contract invokes the production

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Advanced Claude CLI Forwarding

This deterministic offline contract invokes the production

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Plan | doc/03_plan/sys_test/llm_caret_cli_tui_hardening.md |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Scope

This deterministic offline contract invokes the production
`claude_cli_send` function with an existing session, maximum turns, a JSON
schema, the ordered `Read` and `Write` tool vector, and an explicitly allowed
fixture extra argument. The local fixture validates the received process
arguments and returns a structured response.

It proves the shared production sender's advanced one-shot argument boundary;
it does not exercise `bin/caret`, a cached Caret artifact, an installed Claude
binary, authentication, or a network provider.

## Scenarios

### LLM Caret advanced Claude CLI forwarding

### REQ-LLM-CARET-FULL-003: advanced Claude provider request

#### should forward the advanced request through the production Claude sender

- should forward the advanced request through the production Claude sender
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
# @req REQ-SSPEC-SYSTEM
# @req REQ-LLM-CARET-FULL-003
step("should forward the advanced request through the production Claude sender")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-FULL-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2c2dde6a05fdf2312a391fda7700436b4500b85a30452a302655ba10dcaf1442`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c2dde6a05fdf2312a391fda7700436b4500b85a30452a302655ba10dcaf1442`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c2dde6a05fdf2312a391fda7700436b4500b85a30452a302655ba10dcaf1442`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should forward the advanced request through the production Claude sender' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should forward the advanced request through the production Claude sender' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
