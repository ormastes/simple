# Struct Defaults Specification

> Tests covering struct default field values — desugar passthrough.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Struct Defaults Specification

## Scenarios

### struct default field values — desugar passthrough

#### passes struct with single integer default unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- passes struct with single integer default unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes struct with single integer default unchanged")
val input = "struct Counter:\n    count: i64 = 0"
val output = desugar_source(input)
expect(output).to_contain("count: i64 = 0")
```

</details>

#### passes struct with multiple defaults unchanged

- passes struct with multiple defaults unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes struct with multiple defaults unchanged")
val input = "struct Point:\n    x: i64 = 0\n    y: i64 = 0"
val output = desugar_source(input)
expect(output).to_contain("x: i64 = 0")
expect(output).to_contain("y: i64 = 0")
```

</details>

#### passes struct with text default unchanged

- passes struct with text default unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes struct with text default unchanged")
val input = "struct Config:\n    name: text = \"default\""
val output = desugar_source(input)
expect(output).to_contain("name: text = \"default\"")
```

</details>

#### passes struct with bool default unchanged

- passes struct with bool default unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes struct with bool default unchanged")
val input = "struct Flags:\n    enabled: bool = true"
val output = desugar_source(input)
expect(output).to_contain("enabled: bool = true")
```

</details>

#### passes struct with float default unchanged

- passes struct with float default unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes struct with float default unchanged")
val input = "struct Scale:\n    factor: f64 = 1.0"
val output = desugar_source(input)
expect(output).to_contain("factor: f64 = 1.0")
```

</details>

#### passes struct mixing fields with and without defaults

- passes struct mixing fields with and without defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes struct mixing fields with and without defaults")
val input = "struct Node:\n    id: i64\n    count: i64 = 0"
val output = desugar_source(input)
expect(output).to_contain("id: i64")
expect(output).to_contain("count: i64 = 0")
```

</details>

#### does not corrupt struct name when default is present

- does not corrupt struct name when default is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not corrupt struct name when default is present")
val input = "struct Timer:\n    ticks: i64 = 0"
val output = desugar_source(input)
expect(output).to_contain("struct Timer:")
```

</details>

#### preserves default expr after static method extraction

- preserves default expr after static method extraction


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves default expr after static method extraction")
# Pass 1 (static constants) and Pass 2 (static methods) should not
# touch field declarations — only lines inside impl blocks.
val input = "struct Counter:\n    count: i64 = 0\n\nimpl Counter:\n    static fn zero() -> Counter:\n        Counter()"
val output = desugar_source(input)
expect(output).to_contain("count: i64 = 0")
expect(output).to_contain("fn Counter__zero()")
```

</details>

#### preserves default expr after call-site rewriting

- preserves default expr after call-site rewriting


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves default expr after call-site rewriting")
# Pass 4 (rewrite_static_calls) rewrites Type.method() patterns.
# It must not misinterpret the `= value` as a static call.
val input = "struct Config:\n    timeout: i64 = 30"
val output = desugar_source(input)
expect(output).to_contain("timeout: i64 = 30")
```

</details>

#### passes struct with expression default (arithmetic) unchanged

- passes struct with expression default (arithmetic) unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes struct with expression default (arithmetic) unchanged")
val input = "struct Buffer:\n    capacity: i64 = 4 * 1024"
val output = desugar_source(input)
expect(output).to_contain("capacity: i64 = 4 * 1024")
```

</details>

#### passes class body with default fields unchanged

- passes class body with default fields unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes class body with default fields unchanged")
val input = "class Counter:\n    count: i64 = 0\n    fn get() -> i64:\n        self.count"
val output = desugar_source(input)
expect(output).to_contain("count: i64 = 0")
expect(output).to_contain("fn get() -> i64:")
```

</details>

#### preserves default through context_params pass

- preserves default through context_params pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves default through context_params pass")
# Pass -2 (context params) should not touch struct field defaults.
val input = "struct Logger:\n    level: i64 = 1"
val output = desugar_source(input)
expect(output).to_contain("level: i64 = 1")
```

</details>

#### preserves default through trait desugar pass

- preserves default through trait desugar pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves default through trait desugar pass")
# Pass -1 (trait desugar) rewrites trait declarations but must not
# alter struct field default syntax.
val input = "struct Entity:\n    active: bool = true"
val output = desugar_source(input)
expect(output).to_contain("active: bool = true")
```

</details>

#### handles multiple structs each with defaults

- handles multiple structs each with defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple structs each with defaults")
val input = "struct A:\n    x: i64 = 1\n\nstruct B:\n    y: i64 = 2"
val output = desugar_source(input)
expect(output).to_contain("x: i64 = 1")
expect(output).to_contain("y: i64 = 2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/desugar/struct_defaults_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering struct default field values — desugar passthrough.
- struct default field values — desugar passthrough

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `ee6ca2659ffaee423bc1e832e7a87ece1593f823f083db7e1ee9f485c1286c9d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee6ca2659ffaee423bc1e832e7a87ece1593f823f083db7e1ee9f485c1286c9d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee6ca2659ffaee423bc1e832e7a87ece1593f823f083db7e1ee9f485c1286c9d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/desugar/struct_defaults_spec.spl
mirror: doc/06_spec/unit/app/desugar/struct_defaults_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/desugar/struct_defaults_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/desugar/struct_defaults_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/desugar/struct_defaults_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes struct with single integer default unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/struct_defaults_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes struct with multiple defaults unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/struct_defaults_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes struct with text default unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
