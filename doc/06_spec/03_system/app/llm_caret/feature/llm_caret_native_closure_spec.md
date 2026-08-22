# LLM Caret Native Closure Release Gate

> Verifies the llm caret native closure behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Native Closure Release Gate

Verifies the llm caret native closure behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | REQ-LLM-CARET-FULL-003, NFR-LLM-CARET-TUI-006 |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the llm caret native closure behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### LLM Caret Native Closure Release Gate

### REQ-LLM-CARET-FULL-003: Caret is built as a self-hosted native entry closure

#### should build the Caret entry closure from the qualified self-hosted runtime

- Verify: should build the Caret entry closure from the qualified self-hosted runtime
- Prepare the self-hosted native closure
- Build the Caret entry closure
- Check artifact provenance and status
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-FULL-003
step("Verify: should build the Caret entry closure from the qualified self-hosted runtime")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Prepare the self-hosted native closure")
val result = run_caret_native_closure_check()
step("Build the Caret entry closure")
expect(result.stdout).to_contain("closure_status=PASS")
step("Check artifact provenance and status")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### NFR-LLM-CARET-TUI-006: native closure failures remain release-blocking evidence

#### should retain deterministic build and ABI evidence for the qualified artifact

- Verify: should retain deterministic build and ABI evidence for the qualified artifact
- Prepare the self-hosted native closure
- Build the Caret entry closure
- Check artifact provenance and status
   - Expected: result.stderr equals ``
   - Expected: result.exit_code equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LLM-CARET-FULL-003
step("Verify: should retain deterministic build and ABI evidence for the qualified artifact")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("Prepare the self-hosted native closure")
val result = run_caret_native_closure_check()
step("Build the Caret entry closure")
expect(result.stdout).to_contain("closure_status=PASS")
step("Check artifact provenance and status")
expect(result.stderr).to_equal("")
expect(result.exit_code).to_equal(0)  # oracle: pinned constant asserted by this scenario
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


## Related Documentation

- **Requirements:** `REQ-LLM-CARET-FULL-003, NFR-LLM-CARET-TUI-006`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `741417ecf2731382cbbbfa13fc3fd745da8989285c5ca05b30d5bd8226392aa2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `741417ecf2731382cbbbfa13fc3fd745da8989285c5ca05b30d5bd8226392aa2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `741417ecf2731382cbbbfa13fc3fd745da8989285c5ca05b30d5bd8226392aa2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build the Caret entry closure from the qualified self-hosted runtime' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain deterministic build and ABI evidence for the qualified artifact' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
