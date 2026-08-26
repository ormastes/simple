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
| Updated | 2026-08-26 |
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

- Canonical SPipe generation for source `0932dc48848de34289ba7f15008d8bc3e604737efeac14cf46e47f98486631df`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0932dc48848de34289ba7f15008d8bc3e604737efeac14cf46e47f98486631df`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0932dc48848de34289ba7f15008d8bc3e604737efeac14cf46e47f98486631df`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=85 oracle=50
  traceability=60 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl:39:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should forward the advanced request through the production Claude sender' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/llm_caret/feature/llm_caret_claude_cli_advanced_spec.spl:39:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should forward the advanced request through the production Claude sender' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
