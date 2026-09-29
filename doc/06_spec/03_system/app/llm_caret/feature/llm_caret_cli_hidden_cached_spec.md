# LLM Caret Cached Plain-CLI Hidden Command Qualification

> Qualify canonical and alias hidden commands through the actual cached `bin/caret`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Cached Plain-CLI Hidden Command Qualification

Qualify canonical and alias hidden commands through the actual cached `bin/caret`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | REQ-LLM-CARET-HIDDEN-008, REQ-LLM-CARET-FULL-003 |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Scope

Qualify canonical and alias hidden commands through the actual cached `bin/caret`
wrapper in plain non-TTY mode. The checker requires a provenance-qualified
self-hosted artifact, removes provider credentials, disables source fallback,
and retains scrubbed command/output/exit/provenance evidence.

## Scenarios

### LLM Caret Cached Plain-CLI Hidden Command Qualification

### REQ-LLM-CARET-FULL-003: cached artifact is qualified before plain CLI execution

#### should require the pinned cached artifact before hidden-command qualification

- should require the pinned cached artifact before hidden-command qualification
- Load the cached Caret artifact
- Invoke the hidden command through plain CLI
- Check captured output and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-LLM-CARET-HIDDEN-008
# @req REQ-LLM-CARET-FULL-003
step("should require the pinned cached artifact before hidden-command qualification")
step("Load the cached Caret artifact")
val result = run_caret_cli_hidden_cached_case("prerequisites")
step("Invoke the hidden command through plain CLI")
expect(result.stdout).to_contain("case=prerequisites status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)
```

</details>

### REQ-LLM-CARET-HIDDEN-008: hidden and disabled command admission is preserved in plain CLI

#### should reject canonical and alias hidden commands by default

- should reject canonical and alias hidden commands by default
- Load the cached Caret artifact
- Invoke the hidden command through plain CLI
- Check captured output and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject canonical and alias hidden commands by default")
step("Load the cached Caret artifact")
val result = run_caret_cli_hidden_cached_case("default")
step("Invoke the hidden command through plain CLI")
expect(result.stdout).to_contain("case=hidden-canonical-default status=PASS")
expect(result.stdout).to_contain("case=hidden-alias-default status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)
```

</details>

#### should admit canonical and alias hidden commands only when explicitly enabled

- should admit canonical and alias hidden commands only when explicitly enabled
- Load the cached Caret artifact
- Invoke the hidden command through plain CLI
- Check captured output and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should admit canonical and alias hidden commands only when explicitly enabled")
step("Load the cached Caret artifact")
val result = run_caret_cli_hidden_cached_case("enabled")
step("Invoke the hidden command through plain CLI")
expect(result.stdout).to_contain("case=hidden-canonical-enabled status=PASS")
expect(result.stdout).to_contain("case=hidden-alias-enabled status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)
```

</details>

#### should reject canonical and alias hidden commands when the flag is explicitly false

- should reject canonical and alias hidden commands when the flag is explicitly false
- Load the cached Caret artifact
- Invoke the hidden command through plain CLI
- Check captured output and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject canonical and alias hidden commands when the flag is explicitly false")
step("Load the cached Caret artifact")
val result = run_caret_cli_hidden_cached_case("explicit-false")
step("Invoke the hidden command through plain CLI")
expect(result.stdout).to_contain("case=hidden-canonical-false status=PASS")
expect(result.stdout).to_contain("case=hidden-alias-false status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)
```

</details>

#### should reject canonical and alias disabled commands in plain non-TTY mode

- should reject canonical and alias disabled commands in plain non-TTY mode
- Load the cached Caret artifact
- Invoke the hidden command through plain CLI
- Check captured output and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject canonical and alias disabled commands in plain non-TTY mode")
step("Load the cached Caret artifact")
val result = run_caret_cli_hidden_cached_case("disabled")
step("Invoke the hidden command through plain CLI")
expect(result.stdout).to_contain("case=disabled-canonical status=PASS")
expect(result.stdout).to_contain("case=disabled-alias status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `REQ-LLM-CARET-HIDDEN-008, REQ-LLM-CARET-FULL-003`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-HIDDEN-008`
- `REQ-LLM-CARET-FULL-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `843ba3a688d2e00a9bad49ea7c8e99cabc799ce849c3568a19db79f81cdbb854`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `843ba3a688d2e00a9bad49ea7c8e99cabc799ce849c3568a19db79f81cdbb854`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `843ba3a688d2e00a9bad49ea7c8e99cabc799ce849c3568a19db79f81cdbb854`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=75 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require the pinned cached artifact before hidden-command qualification' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should require the pinned cached artifact before hidden-command qualification' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:61:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject canonical and alias hidden commands by default' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject canonical and alias hidden commands by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:73:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should admit canonical and alias hidden commands only when explicitly enabled' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should admit canonical and alias hidden commands only when explicitly enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject canonical and alias hidden commands when the flag is explicitly false' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:97:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject canonical and alias disabled commands in plain non-TTY mode' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
