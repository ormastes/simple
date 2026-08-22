# LLM Caret Cached CLI Qualification

> Verifies the llm caret cli cached behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Cached CLI Qualification

Verifies the llm caret cli cached behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | REQ-LLM-CARET-FULL-003, NFR-LLM-CARET-TUI-006 |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the llm caret cli cached behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### LLM Caret Cached CLI Qualification

### REQ-LLM-CARET-FULL-003: cached Caret CLI accepts the offline Claude provider

#### should verify the cached artifact and its provenance before qualification

- Verify: should verify the cached artifact and its provenance before qualification
- Load the cached Caret artifact
- Invoke the offline Caret CLI provider
- Check captured output and status
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-FULL-003
step("Verify: should verify the cached artifact and its provenance before qualification")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the cached Caret artifact")
val result = run_caret_cli_cached_case("prerequisites")
step("Invoke the offline Caret CLI provider")
expect(result.stdout).to_contain("case=prerequisites status=PASS")
expect(result.stdout).to_contain("cached_artifact=")
expect(result.stdout).to_contain("provenance_file=")
expect(result.stdout).to_contain("source_commit_check=matched")
expect(result.stdout).to_contain("verified_binary_sha256=")
expect(result.stdout).to_contain("verified_runtime_path=")
expect(result.stdout).to_contain("verified_runtime_sha256=")
expect(result.stdout).to_contain("runtime=pure-simple-self-hosted")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### should return the offline Claude response from the cached executable

- Verify: should return the offline Claude response from the cached executable
- Load the cached Caret artifact
- Invoke the offline Caret CLI provider
- Check captured output and status
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-FULL-003
step("Verify: should return the offline Claude response from the cached executable")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the cached Caret artifact")
val result = run_caret_cli_cached_case("offline-claude")
step("Invoke the offline Caret CLI provider")
expect(result.stdout).to_contain("case=offline-claude status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### NFR-LLM-CARET-TUI-006: cached qualification is fail closed and captured

#### should preserve cached provider failure and usage evidence

- Verify: should preserve cached provider failure and usage evidence
- Load the cached Caret artifact
- Invoke the offline Caret CLI provider
- Check captured output and status
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-FULL-003
step("Verify: should preserve cached provider failure and usage evidence")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Load the cached Caret artifact")
val result = run_caret_cli_cached_case("failure-usage")
step("Invoke the offline Caret CLI provider")
expect(result.stdout).to_contain("case=provider-error status=PASS")
expect(result.stdout).to_contain("case=unknown-option status=PASS")
step("Check captured output and status")
expect(result.stdout).to_contain("evidence_status=PASS")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
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

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0915a770c44d8405b77b95ae342762f60a7d9a88637740687ab86b31373d454a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0915a770c44d8405b77b95ae342762f60a7d9a88637740687ab86b31373d454a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0915a770c44d8405b77b95ae342762f60a7d9a88637740687ab86b31373d454a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should verify the cached artifact and its provenance before qualification' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return the offline Claude response from the cached executable' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_cli_cached_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve cached provider failure and usage evidence' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
