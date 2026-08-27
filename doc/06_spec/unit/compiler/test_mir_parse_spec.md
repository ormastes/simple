# test_mir_parse_spec

> Generates SPIR-V code for Vulkan compute shaders.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_mir_parse_spec

Generates SPIR-V code for Vulkan compute shaders.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/test_mir_parse_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

Generates SPIR-V code for Vulkan compute shaders.

    SPIR-V is a binary format, but we generate human-readable
    assembly that can be assembled with spirv-as or used for debugging.

    Structure:
    1. Capabilities and extensions
    2. Memory model
    3. Entry point declaration
    4. Decorations
    5. Type declarations
    6. Constants
    7. Global variables
    8. Functions

    This builder generates SPIR-V assembly (text) that can be
    assembled to binary using spirv-as from SPIRV-Tools.

## Scenarios

### parse test

#### loads

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads")
assert_equal(1, 1)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a6454dd0648a092974ea78a8c8204b6af73162b4e8fe83bdec41cd9a9dd84fdc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6454dd0648a092974ea78a8c8204b6af73162b4e8fe83bdec41cd9a9dd84fdc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6454dd0648a092974ea78a8c8204b6af73162b4e8fe83bdec41cd9a9dd84fdc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/unit/compiler/test_mir_parse_spec.spl
mirror: doc/06_spec/unit/compiler/test_mir_parse_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/test_mir_parse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/test_mir_parse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/test_mir_parse_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
