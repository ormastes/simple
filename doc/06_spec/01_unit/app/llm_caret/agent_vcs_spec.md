# Agent Vcs Specification

> Tests covering LLM Caret agent vcs parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Agent Vcs Specification

## Scenarios

### LLM Caret agent vcs parsing

#### parses changed file lines and dedupes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses changed file lines and dedupes
   - Expected: changes.agent_id equals `agent-1`
   - Expected: changes.changed_files.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses changed file lines and dedupes")
val out = "src/a.spl\nsrc/b.spl\nsrc/a.spl\n"
val changes = parse_vcs_changed_files("agent-1", out)
expect(changes.agent_id).to_equal("agent-1")
expect(changes.changed_files.len()).to_equal(2)
expect(changes.changed_files).to_contain("src/a.spl")
expect(changes.changed_files).to_contain("src/b.spl")
```

</details>

#### drops warning and error banner lines from stdout

- drops warning and error banner lines from stdout
   - Expected: changes.changed_files.len() equals `1`
   - Expected: changes.changed_files[0] equals `src/real.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("drops warning and error banner lines from stdout")
val out = "Warning: something\nsrc/real.spl\nError: broken\nHint: try this\n"
val changes = parse_vcs_changed_files("agent-1", out)
expect(changes.changed_files.len()).to_equal(1)
expect(changes.changed_files[0]).to_equal("src/real.spl")
```

</details>

#### returns empty set for empty stdout

- returns empty set for empty stdout
   - Expected: changes.changed_files.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns empty set for empty stdout")
val changes = parse_vcs_changed_files("agent-1", "")
expect(changes.changed_files.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/agent_vcs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LLM Caret agent vcs parsing.
- LLM Caret agent vcs parsing

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a9d339d78ddaca0e322205966f56a39b6dbaf12e7bff932eb341174daa087666`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a9d339d78ddaca0e322205966f56a39b6dbaf12e7bff932eb341174daa087666`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a9d339d78ddaca0e322205966f56a39b6dbaf12e7bff932eb341174daa087666`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/llm_caret/agent_vcs_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/agent_vcs_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/agent_vcs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/agent_vcs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/agent_vcs_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/agent_vcs_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses changed file lines and dedupes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/agent_vcs_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drops warning and error banner lines from stdout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/agent_vcs_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty set for empty stdout' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
