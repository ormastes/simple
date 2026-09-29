# Function Local Use Discarded Specification

> Tests covering driver imports discarded by the parser (repro), no function-local `use` remains under 80.driver (generalization).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Function Local Use Discarded Specification

## Scenarios

### driver imports discarded by the parser (repro)

#### driver_types.spl imports CompileOptionsHash at module scope

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- driver_types.spl imports CompileOptionsHash at module scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("driver_types.spl imports CompileOptionsHash at module scope")
val src = function_local_use_spec_source("src/compiler/80.driver/driver_types.spl")
expect(src).to_contain("\nuse compiler.driver.cache.compile_options_hash.\{CompileOptionsHash, compile_options_hash_compute\}")
# Non-vacuity: both names are still actually used by the file.
assert_true(src.contains("-> CompileOptionsHash"))
assert_true(src.contains("compile_options_hash_compute("))
```

</details>

### no function-local `use` remains under 80.driver (generalization)

#### driver_types.spl has none

- driver_types.spl has none


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("driver_types.spl has none")
expect(function_local_use_spec_indented_use_count(
    function_local_use_spec_source("src/compiler/80.driver/driver_types.spl"))).to_equal(0)
```

</details>

#### driver_api_project_build.spl has none

- driver_api_project_build.spl has none


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("driver_api_project_build.spl has none")
expect(function_local_use_spec_indented_use_count(
    function_local_use_spec_source("src/compiler/80.driver/driver_api_project_build.spl"))).to_equal(0)
```

</details>

#### project.spl has none

- project.spl has none


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("project.spl has none")
expect(function_local_use_spec_indented_use_count(
    function_local_use_spec_source("src/compiler/80.driver/project.spl"))).to_equal(0)
```

</details>

#### watcher/watcher_client.spl has none

- watcher/watcher_client.spl has none


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("watcher/watcher_client.spl has none")
expect(function_local_use_spec_indented_use_count(
    function_local_use_spec_source("src/compiler/80.driver/watcher/watcher_client.spl"))).to_equal(0)
```

</details>

#### cache/compile_options_hash.spl has none

- cache/compile_options_hash.spl has none


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cache/compile_options_hash.spl has none")
expect(function_local_use_spec_indented_use_count(
    function_local_use_spec_source("src/compiler/80.driver/cache/compile_options_hash.spl"))).to_equal(0)
```

</details>

#### cache/cache_validator.spl has none

- cache/cache_validator.spl has none


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cache/cache_validator.spl has none")
expect(function_local_use_spec_indented_use_count(
    function_local_use_spec_source("src/compiler/80.driver/cache/cache_validator.spl"))).to_equal(0)
```

</details>

#### the counter is not vacuously zero

- the counter is not vacuously zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the counter is not vacuously zero")
# A file that genuinely contains an indented `use` must be counted, so a
# broken scanner cannot pass the six checks above by returning 0 always.
expect(function_local_use_spec_indented_use_count(
    "fn f():\n    use a.b.\{c\}\n    c()")).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/function_local_use_discarded_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering driver imports discarded by the parser (repro), no function-local `use` remains under 80.driver (generalization).
- driver imports discarded by the parser (repro)
- no function-local `use` remains under 80.driver (generalization)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `f80d934469b5d05f0bfd4f44cd7c40e3db887b71e3a08be72463d94135cf79b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f80d934469b5d05f0bfd4f44cd7c40e3db887b71e3a08be72463d94135cf79b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f80d934469b5d05f0bfd4f44cd7c40e3db887b71e3a08be72463d94135cf79b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/function_local_use_discarded_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/function_local_use_discarded_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/function_local_use_discarded_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/function_local_use_discarded_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/function_local_use_discarded_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'driver_types.spl imports CompileOptionsHash at module scope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/function_local_use_discarded_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'driver_types.spl has none' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/function_local_use_discarded_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'driver_api_project_build.spl has none' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
