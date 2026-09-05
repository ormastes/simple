# LLM Caret Native Closure Release Gate

> Build and inspect the production Caret entry closure only with a supplied

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLM Caret Native Closure Release Gate

Build and inspect the production Caret entry closure only with a supplied

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | REQ-LLM-CARET-FULL-003, NFR-LLM-CARET-TUI-006 |
| Source | `test/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Scope

Build and inspect the production Caret entry closure only with a supplied
simple-core archive and a self-hosted runtime. Bootstrap/seed runtimes and stub
fallback are rejected. The checker preserves build and ABI evidence under
`build/test-artifacts/03_system/app/llm_caret/feature/llm_caret_native_closure/`.

## Scenarios

### LLM Caret Native Closure Release Gate

### REQ-LLM-CARET-FULL-003: Caret is built as a self-hosted native entry closure

#### should build the Caret entry closure from the qualified self-hosted runtime

- should build the Caret entry closure from the qualified self-hosted runtime
- Prepare the self-hosted native closure
- Build the Caret entry closure
- Check artifact provenance and status
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LLM-CARET-FULL-003 REQ-SSPEC-SYSTEM
step("should build the Caret entry closure from the qualified self-hosted runtime")
step("Prepare the self-hosted native closure")
val result = run_caret_native_closure_check()
step("Build the Caret entry closure")
expect(result.stdout).to_contain("closure_status=PASS")
step("Check artifact provenance and status")
expect(result.exit_code).to_equal(0)
```

</details>

### NFR-LLM-CARET-TUI-006: native closure failures remain release-blocking evidence

#### should retain deterministic build and ABI evidence for the qualified artifact

- should retain deterministic build and ABI evidence for the qualified artifact
- Prepare the self-hosted native closure
- Build the Caret entry closure
- Check artifact provenance and status
   - Expected: result.stderr equals ``
   - Expected: result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req NFR-LLM-CARET-TUI-006 REQ-SSPEC-SYSTEM
step("should retain deterministic build and ABI evidence for the qualified artifact")
step("Prepare the self-hosted native closure")
val result = run_caret_native_closure_check()
step("Build the Caret entry closure")
expect(result.stdout).to_contain("closure_status=PASS")
step("Check artifact provenance and status")
expect(result.stderr).to_equal("")
expect(result.exit_code).to_equal(0)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-LLM-CARET-FULL-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `989235514c94f640de87f05193a8db3c16efe720af509f58d4b19b7e8a51328e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `989235514c94f640de87f05193a8db3c16efe720af509f58d4b19b7e8a51328e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `989235514c94f640de87f05193a8db3c16efe720af509f58d4b19b7e8a51328e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.spl
mirror: doc/06_spec/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build the Caret entry closure from the qualified self-hosted runtime' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should build the Caret entry closure from the qualified self-hosted runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.spl:55:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain deterministic build and ABI evidence for the qualified artifact' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/llm_caret/feature/llm_caret_native_closure_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain deterministic build and ABI evidence for the qualified artifact' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
