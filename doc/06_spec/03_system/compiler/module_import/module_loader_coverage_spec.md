# Module Loader Coverage Specification

> Tests covering Module Loader Coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Loader Coverage Specification

## Scenarios

### Module Loader Coverage

#### check_coverage API returns valid result for loader line coverage

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- check_coverage API returns valid result for loader line coverage
   - Expected: result.coverage_type equals `line`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("check_coverage API returns valid result for loader line coverage")
val result = check_coverage("line", "src/core/interpreter/module_loader.spl", minimum: 0.0)
expect(result.coverage_type).to_equal("line")
print "  module_loader.spl line coverage: {result.actual}%  files_matched={result.files_matched}"
```

</details>

#### check_coverage API returns valid result for loader branch coverage

- check_coverage API returns valid result for loader branch coverage
   - Expected: result.coverage_type equals `branch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("check_coverage API returns valid result for loader branch coverage")
val result = check_coverage("branch", "src/core/interpreter/module_loader.spl", minimum: 0.0)
expect(result.coverage_type).to_equal("branch")
print "  module_loader.spl branch coverage: {result.actual}%  files_matched={result.files_matched}"
```

</details>

#### check_coverage API returns valid result for loader function coverage

- check_coverage API returns valid result for loader function coverage
   - Expected: result.coverage_type equals `function`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("check_coverage API returns valid result for loader function coverage")
val result = check_coverage("function", "src/core/interpreter/module_loader.spl", minimum: 0.0)
expect(result.coverage_type).to_equal("function")
print "  module_loader.spl function coverage: {result.actual}%  files_matched={result.files_matched}"
```

</details>

#### check_coverage API returns valid result for wildcard loader pattern

- check_coverage API returns valid result for wildcard loader pattern
   - Expected: result.coverage_type equals `line`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("check_coverage API returns valid result for wildcard loader pattern")
val result = check_coverage("line", "src/core/interpreter/**", minimum: 0.0)
expect(result.coverage_type).to_equal("line")
print "  src/core/interpreter/** line coverage: {result.actual}%  files_matched={result.files_matched}"
```

</details>

#### coverage_type field is preserved on error result

- coverage_type field is preserved on error result
   - Expected: result.coverage_type equals `branch`
   - Expected: result.pattern equals `src/core/interpreter/module_loader.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("coverage_type field is preserved on error result")
val result = check_coverage("branch", "src/core/interpreter/module_loader.spl", minimum: 0.0)
expect(result.coverage_type).to_equal("branch")
expect(result.pattern).to_equal("src/core/interpreter/module_loader.spl")
```

</details>

#### minimum_check field is set correctly

- minimum_check field is set correctly
   - Expected: result.minimum_check is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("minimum_check field is set correctly")
val result = check_coverage("line", "src/core/interpreter/module_loader.spl", minimum: 0.0, minimum_check: true)
expect(result.minimum_check).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/module_import/module_loader_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Module Loader Coverage.
- Module Loader Coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c9e2e4a4c002a489f2f840c509c9b9cb9cbd433bfc8be4003f4592c1578c622d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c9e2e4a4c002a489f2f840c509c9b9cb9cbd433bfc8be4003f4592c1578c622d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c9e2e4a4c002a489f2f840c509c9b9cb9cbd433bfc8be4003f4592c1578c622d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/module_import/module_loader_coverage_spec.spl
mirror: doc/06_spec/03_system/compiler/module_import/module_loader_coverage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/module_import/module_loader_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/module_import/module_loader_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/module_import/module_loader_coverage_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'check_coverage API returns valid result for loader line coverage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/module_import/module_loader_coverage_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'check_coverage API returns valid result for loader branch coverage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/module_import/module_loader_coverage_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'check_coverage API returns valid result for loader function coverage' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
