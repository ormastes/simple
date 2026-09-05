# LLM Caret Cached CLI Qualification

> Exercise the shipped cached Caret CLI through the fail-closed qualification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Cached CLI Qualification

Exercise the shipped cached Caret CLI through the fail-closed qualification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | REQ-LLM-CARET-FULL-003, NFR-LLM-CARET-TUI-006 |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scope

Exercise the shipped cached Caret CLI through the fail-closed qualification
checker. The checker validates artifact-root and provenance markers before it
accepts any cached-provider result, then saves command and artifact evidence
under `build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_cli_cached/`.
All provider traffic is supplied by the offline Claude fixture.

## Scenarios

### LLM Caret Cached CLI Qualification

### REQ-LLM-CARET-FULL-003: cached Caret CLI accepts the offline Claude provider

#### should verify the cached artifact and its provenance before qualification
#### should return the offline Claude response from the cached executable

- should return the offline Claude response from the cached executable
- Load the cached Caret artifact
- Invoke the offline Caret CLI provider
- Check captured output and status
   - Expected: result.exit_code equals `0`

The checker runs a deterministic provider failure and unknown-option rejection.
It requires their expected nonzero exits while the enclosing evidence checker
returns zero, and it rejects a retained fixture secret.

## Execution Boundary

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return the offline Claude response from the cached executable")
step("Load the cached Caret artifact")
val result = run_caret_cli_cached_case("offline-claude")
step("Invoke the offline Caret CLI provider")
expect(result.stdout).to_contain("case=offline-claude status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)
```

</details>

### NFR-LLM-CARET-TUI-006: cached qualification is fail closed and captured

#### should preserve cached provider failure and usage evidence

- should preserve cached provider failure and usage evidence
- Load the cached Caret artifact
- Invoke the offline Caret CLI provider
- Check captured output and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve cached provider failure and usage evidence")
step("Load the cached Caret artifact")
val result = run_caret_cli_cached_case("failure-usage")
step("Invoke the offline Caret CLI provider")
expect(result.stdout).to_contain("case=provider-error status=PASS")
expect(result.stdout).to_contain("case=unknown-option status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)
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


## Related Documentation

- **Requirements:** `REQ-LLM-CARET-FULL-003, NFR-LLM-CARET-TUI-006`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-FULL-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d0b87f429c7a6dc536cb950ef658ffd72d743bf7585c7fadc616b0cabfbe175f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d0b87f429c7a6dc536cb950ef658ffd72d743bf7585c7fadc616b0cabfbe175f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d0b87f429c7a6dc536cb950ef658ffd72d743bf7585c7fadc616b0cabfbe175f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.md (current)
findings: 10 blockers: 1
  narrative=100 structure=75 oracle=80
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl:52:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should verify the cached artifact and its provenance before qualification' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should verify the cached artifact and its provenance before qualification' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return the offline Claude response from the cached executable' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should return the offline Claude response from the cached executable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl:84:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve cached provider failure and usage evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve cached provider failure and usage evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
