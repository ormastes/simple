# test_mir_parse_spec

> Generates SPIR-V code for Vulkan compute shaders.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_mir_parse_spec

Generates SPIR-V code for Vulkan compute shaders.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/test_mir_parse_spec.spl` |
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


- parse this very file (class + Dict generics) through the real parser
   - Expected: parser_has_errors() is false
   - Expected: parser_get_errors().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parse this very file (class + Dict generics) through the real parser")
val source = file_read("test/01_unit/compiler/test_mir_parse_spec.spl")
parse_module(source, "test_mir_parse_spec.spl")
expect(parser_has_errors()).to_equal(false)
expect(parser_get_errors().len()).to_equal(0)
```

</details>

#### reports errors for a syntactically broken module

- parse a broken fixture, assert the parser reports it
   - Expected: parser_has_errors() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parse a broken fixture, assert the parser reports it")
parse_module("fn broken( <<< !!\n", "broken_fixture.spl")
expect(parser_has_errors()).to_equal(true)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `17242afaf9a32d5a92707420a2eab0f6748e0b2d3689447af4b05a4d91010e39`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17242afaf9a32d5a92707420a2eab0f6748e0b2d3689447af4b05a4d91010e39`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17242afaf9a32d5a92707420a2eab0f6748e0b2d3689447af4b05a4d91010e39`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/test_mir_parse_spec.spl
mirror: doc/06_spec/01_unit/compiler/test_mir_parse_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/test_mir_parse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/test_mir_parse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/test_mir_parse_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/test_mir_parse_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/test_mir_parse_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports errors for a syntactically broken module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
