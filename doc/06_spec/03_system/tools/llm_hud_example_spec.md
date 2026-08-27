# Llm Hud Example Specification

> Tests covering llm_hud example.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Hud Example Specification

## Scenarios

### llm_hud example

#### renders codex statusline output

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders codex statusline output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders codex statusline output")
val (stdout, stderr, code) = run_hud(["--provider", "codex", "--mode", "statusline", "--no-color"])
expect(code).to_equal(0)
expect(stdout).to_contain("[Codex]")
expect(stdout).to_contain("tool ")
```

</details>

#### renders gemini fallback output

- renders gemini fallback output
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("renders gemini fallback output")
val (stdout, stderr, code) = run_hud(["--provider", "gemini", "--mode", "statusline", "--no-color"])
expect(code).to_equal(0)
expect(stdout).to_contain("[Gemini]")
expect(stdout).to_contain("Gemini")
```

</details>

#### prints help

- prints help
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prints help")
val (stdout, stderr, code) = run_hud(["--help"])
expect(code).to_equal(0)
expect(stdout).to_contain("Simple LLM HUD")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm_hud_example_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering llm_hud example.
- llm_hud example

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

- Canonical SPipe generation for source `466893753ac0171d89bc8383e51a8cb91fa95e2fd9f9a166072ba4560f304463`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `466893753ac0171d89bc8383e51a8cb91fa95e2fd9f9a166072ba4560f304463`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `466893753ac0171d89bc8383e51a8cb91fa95e2fd9f9a166072ba4560f304463`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm_hud_example_spec.spl
mirror: doc/06_spec/03_system/tools/llm_hud_example_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm_hud_example_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm_hud_example_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm_hud_example_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm_hud_example_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders codex statusline output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm_hud_example_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders gemini fallback output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm_hud_example_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
