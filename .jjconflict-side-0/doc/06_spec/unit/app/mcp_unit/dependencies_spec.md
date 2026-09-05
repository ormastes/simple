# Dependencies Specification

> Tests covering Simple dependency extraction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dependencies Specification

## Scenarios

### Simple dependency extraction

<details>
<summary>Advanced: parses use statements</summary>

#### parses use statements _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses use statements
   - Expected: has_use is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses use statements")
val source_line = "use std.io as io"
val has_use = source_line.starts_with("use ")
expect(has_use).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: parses selective imports</summary>

#### parses selective imports _(slow)_

- parses selective imports
   - Expected: has_use is true
   - Expected: has_selective is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses selective imports")
val source_line = "use std.math.{abs, max}"
val has_use = source_line.starts_with("use ")
val has_selective = source_line.contains("{")
expect(has_use).to_equal(true)
expect(has_selective).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: parses from-use imports</summary>

#### parses from-use imports _(slow)_

- parses from-use imports
   - Expected: has_from is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses from-use imports")
val source_line = "from utils.helpers use trim, slug"
val has_from = source_line.starts_with("from ")
expect(has_from).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: parses pub use reexports</summary>

#### parses pub use reexports _(slow)_

- parses pub use reexports
   - Expected: has_pub_use is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses pub use reexports")
val source_line = "pub use app.api"
val has_pub_use = source_line.starts_with("pub use ")
expect(has_pub_use).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: detects self-referential cycle</summary>

#### detects self-referential cycle _(slow)_

- detects self-referential cycle
   - Expected: is_cycle is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects self-referential cycle")
val module_name = "core"
val import_name = "core"
val is_cycle = module_name == import_name
expect(is_cycle).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: detects no cycle for different modules</summary>

#### detects no cycle for different modules _(slow)_

- detects no cycle for different modules
   - Expected: is_cycle is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects no cycle for different modules")
val module_name = "app"
val import_name = "std"
val is_cycle = module_name == import_name
expect(is_cycle).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: tracks symbol usage by function</summary>

#### tracks symbol usage by function _(slow)_

- tracks symbol usage by function
   - Expected: io_fn equals `run`
   - Expected: abs_fn equals `run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks symbol usage by function")
val usage = jo2(jp("std.io", js("run")), jp("abs", js("run")))
val io_fn = extract_json_string(usage, "std.io")
val abs_fn = extract_json_string(usage, "abs")
expect(io_fn).to_equal("run")
expect(abs_fn).to_equal("run")
```

</details>


</details>

<details>
<summary>Advanced: tracks multiple functions using same symbol</summary>

#### tracks multiple functions using same symbol _(slow)_

- tracks multiple functions using same symbol
   - Expected: used_by_helper is true
   - Expected: used_by_formatter is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks multiple functions using same symbol")
val slug_usage = "helper,formatter"
val used_by_helper = slug_usage.contains("helper")
val used_by_formatter = slug_usage.contains("formatter")
expect(used_by_helper).to_equal(true)
expect(used_by_formatter).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: extracts module path from qualified import</summary>

#### extracts module path from qualified import _(slow)_

- extracts module path from qualified import
   - Expected: has_dots is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts module path from qualified import")
val import_path = "foo.bar.baz"
val has_dots = import_path.contains(".")
expect(has_dots).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: identifies aliased imports</summary>

#### identifies aliased imports _(slow)_

- identifies aliased imports
   - Expected: has_alias is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies aliased imports")
val source_line = "use std.io as io"
val has_alias = source_line.contains(" as ")
expect(has_alias).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/dependencies_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple dependency extraction.
- Simple dependency extraction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
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

- Canonical SPipe generation for source `28518e101f6748e74d4bbaeb040cbbb4ce53dcd0bdda1f9cc4a088a4ffcfd2bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28518e101f6748e74d4bbaeb040cbbb4ce53dcd0bdda1f9cc4a088a4ffcfd2bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28518e101f6748e74d4bbaeb040cbbb4ce53dcd0bdda1f9cc4a088a4ffcfd2bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/dependencies_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/dependencies_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/dependencies_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/dependencies_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/dependencies_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses use statements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/dependencies_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses selective imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/dependencies_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses from-use imports' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
