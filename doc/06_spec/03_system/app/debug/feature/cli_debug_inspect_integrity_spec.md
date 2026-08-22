# CLI evidence inspection integrity

> Verifies the cli debug inspect integrity behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI evidence inspection integrity

Verifies the cli debug inspect integrity behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/debug/feature/cli_debug_inspect_integrity_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the cli debug inspect integrity behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### simple debug inspect evidence integrity

#### rejects a tampered retained artifact at the operator CLI boundary

- Verify: rejects a tampered retained artifact at the operator CLI boundary
   - Expected: exit_code != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-008 REQ-009 REQ-014
step("Verify: rejects a tampered retained artifact at the operator CLI boundary")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val root = "build/test-cli-debug-inspect-integrity-system"
tampered_bundle(root)
val (stdout, stderr, exit_code) = process_run(
    "bin/simple", ["run", "src/app/cli_debug/main.spl", "inspect", root])
expect(exit_code != 0).to_equal(true)
expect(stdout + stderr).to_contain("artifact digest mismatch")
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


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fd53f6baeb5dcc66422e200805cb089a8203c4cf2628bb6e29710d7f6fd7d5da`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fd53f6baeb5dcc66422e200805cb089a8203c4cf2628bb6e29710d7f6fd7d5da`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fd53f6baeb5dcc66422e200805cb089a8203c4cf2628bb6e29710d7f6fd7d5da`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/debug/feature/cli_debug_inspect_integrity_spec.spl
mirror: doc/06_spec/03_system/app/debug/feature/cli_debug_inspect_integrity_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/debug/feature/cli_debug_inspect_integrity_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/debug/feature/cli_debug_inspect_integrity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/debug/feature/cli_debug_inspect_integrity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
