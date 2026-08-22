# LLM Caret Cached Plain-CLI Hidden Command Qualification

> Verifies the llm caret cli hidden cached behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Cached Plain-CLI Hidden Command Qualification

Verifies the llm caret cli hidden cached behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | REQ-LLM-CARET-HIDDEN-008, REQ-LLM-CARET-FULL-003 |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the llm caret cli hidden cached behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### LLM Caret Cached Plain-CLI Hidden Command Qualification

### REQ-LLM-CARET-FULL-003: cached artifact is qualified before plain CLI execution

#### should require the pinned cached artifact before hidden-command qualification

- Verify: should require the pinned cached artifact before hidden-command qualification
- Load the cached Caret artifact
- Invoke the hidden command through plain CLI
- Check captured output and status
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-HIDDEN-008 REQ-LLM-CARET-FULL-003
step("Verify: should require the pinned cached artifact before hidden-command qualification")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the cached Caret artifact")
val result = run_caret_cli_hidden_cached_case("prerequisites")
step("Invoke the hidden command through plain CLI")
expect(result.stdout).to_contain("case=prerequisites status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### REQ-LLM-CARET-HIDDEN-008: hidden and disabled command admission is preserved in plain CLI

#### should reject canonical and alias hidden commands by default

- Verify: should reject canonical and alias hidden commands by default
- Load the cached Caret artifact
- Invoke the hidden command through plain CLI
- Check captured output and status
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-HIDDEN-008 REQ-LLM-CARET-FULL-003
step("Verify: should reject canonical and alias hidden commands by default")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the cached Caret artifact")
val result = run_caret_cli_hidden_cached_case("default")
step("Invoke the hidden command through plain CLI")
expect(result.stdout).to_contain("case=hidden-canonical-default status=PASS")
expect(result.stdout).to_contain("case=hidden-alias-default status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should admit canonical and alias hidden commands only when explicitly enabled

- Verify: should admit canonical and alias hidden commands only when explicitly enabled
- Load the cached Caret artifact
- Invoke the hidden command through plain CLI
- Check captured output and status
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-HIDDEN-008 REQ-LLM-CARET-FULL-003
step("Verify: should admit canonical and alias hidden commands only when explicitly enabled")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the cached Caret artifact")
val result = run_caret_cli_hidden_cached_case("enabled")
step("Invoke the hidden command through plain CLI")
expect(result.stdout).to_contain("case=hidden-canonical-enabled status=PASS")
expect(result.stdout).to_contain("case=hidden-alias-enabled status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should reject canonical and alias hidden commands when the flag is explicitly false

- Verify: should reject canonical and alias hidden commands when the flag is explicitly false
- Load the cached Caret artifact
- Invoke the hidden command through plain CLI
- Check captured output and status
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-HIDDEN-008 REQ-LLM-CARET-FULL-003
step("Verify: should reject canonical and alias hidden commands when the flag is explicitly false")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the cached Caret artifact")
val result = run_caret_cli_hidden_cached_case("explicit-false")
step("Invoke the hidden command through plain CLI")
expect(result.stdout).to_contain("case=hidden-canonical-false status=PASS")
expect(result.stdout).to_contain("case=hidden-alias-false status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should reject canonical and alias disabled commands in plain non-TTY mode

- Verify: should reject canonical and alias disabled commands in plain non-TTY mode
- Load the cached Caret artifact
- Invoke the hidden command through plain CLI
- Check captured output and status
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-HIDDEN-008 REQ-LLM-CARET-FULL-003
step("Verify: should reject canonical and alias disabled commands in plain non-TTY mode")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the cached Caret artifact")
val result = run_caret_cli_hidden_cached_case("disabled")
step("Invoke the hidden command through plain CLI")
expect(result.stdout).to_contain("case=disabled-canonical status=PASS")
expect(result.stdout).to_contain("case=disabled-alias status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `67463568c012e5b6b1cd778443f220723a05d2c2a996f12f2a46ca92a12505ac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `67463568c012e5b6b1cd778443f220723a05d2c2a996f12f2a46ca92a12505ac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `67463568c012e5b6b1cd778443f220723a05d2c2a996f12f2a46ca92a12505ac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require the pinned cached artifact before hidden-command qualification' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject canonical and alias hidden commands by default' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should admit canonical and alias hidden commands only when explicitly enabled' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:96:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject canonical and alias hidden commands when the flag is explicitly false' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_hidden_cached_spec.spl:109:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject canonical and alias disabled commands in plain non-TTY mode' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
