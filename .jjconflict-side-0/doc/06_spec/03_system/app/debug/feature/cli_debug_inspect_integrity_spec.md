# CLI evidence inspection integrity

> The operator-facing `simple debug inspect <bundle>` command must reject a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI evidence inspection integrity

The operator-facing `simple debug inspect <bundle>` command must reject a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/debug/feature/cli_debug_inspect_integrity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The operator-facing `simple debug inspect <bundle>` command must reject a
retained artifact whose bytes no longer match the exact digest in the bundle
manifest. A parsed manifest is not sufficient evidence integrity.

## Scenarios

### simple debug inspect evidence integrity

#### rejects a tampered retained artifact at the operator CLI boundary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a tampered retained artifact at the operator CLI boundary
   - Expected: exit_code != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a tampered retained artifact at the operator CLI boundary")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-008`
- `REQ-009`
- `REQ-014`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a412f32420faec72760fd019f799f99a94748b7fe827c1ec0d18c93e4c0e42f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a412f32420faec72760fd019f799f99a94748b7fe827c1ec0d18c93e4c0e42f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a412f32420faec72760fd019f799f99a94748b7fe827c1ec0d18c93e4c0e42f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/debug/feature/cli_debug_inspect_integrity_spec.spl
mirror: doc/06_spec/03_system/app/debug/feature/cli_debug_inspect_integrity_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=89; blocker cap makes effective=49
doc/06_spec/03_system/app/debug/feature/cli_debug_inspect_integrity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/debug/feature/cli_debug_inspect_integrity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/debug/feature/cli_debug_inspect_integrity_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/debug/feature/cli_debug_inspect_integrity_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a tampered retained artifact at the operator CLI boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
