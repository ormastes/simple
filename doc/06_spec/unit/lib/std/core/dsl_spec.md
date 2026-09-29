# Dsl Specification

> Tests covering Context blocks, Method missing, Fluent interfaces.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dsl Specification

## Scenarios

### Context blocks

#### provides context-aware building

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- provides context-aware building


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides context-aware building")
val builder = ContextBuilder.new()
expect builder.is_empty() == true

builder.set("name", "Alice")
builder.set("age", 30)

expect builder.has("name") == true
expect builder.get("name") == "Alice"
expect builder.size() == 2
```

</details>

### Method missing

#### handles undefined methods

- handles undefined methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles undefined methods")
var called_name = ""
var called_args = []

val handler = fn(name, args):
    called_name = name
    called_args = args
    42
val proxy = DynamicProxy.new(handler)

val result = proxy.method_missing("test_method", [1, 2, 3])
expect result == 42
expect called_name == "test_method"
```

</details>

#### enables dynamic proxies

- enables dynamic proxies


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables dynamic proxies")
val handler = \name, args: "handled"
val proxy = DynamicProxy.new(handler)

expect proxy.has_handler() == true
val result = proxy.call_handler("any_method", [])
expect result == "handled"
```

</details>

#### supports attribute dictionaries

- supports attribute dictionaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports attribute dictionaries")
val obj = AttributeDict.new()
expect obj.is_empty() == true

obj.__setattr__("name", "Alice")
val name = obj.__getattr__("name")
expect name == "Alice"
expect obj.has_attr("name") == true
```

</details>

### Fluent interfaces

#### enables method chaining

- enables method chaining


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables method chaining")
val query = QueryBuilder.new()
query.select(["name", "age"])
query.from_table("users")

expect query.has_table() == true
expect query.field_count() == 2
expect query.is_valid() == true
```

</details>

#### supports pipeline transformations

- supports pipeline transformations


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports pipeline transformations")
val pipe = Pipeline.new([1, 2, 3, 4, 5])
expect pipe.size() == 5

pipe.filter(_1 > 2)
expect pipe.size() == 3

val result = pipe.collect()
expect len(result) == 3
expect result[0] == 3
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/std/core/dsl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Context blocks, Method missing, Fluent interfaces.
- Context blocks
- Method missing
- Fluent interfaces

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1941c3438b7f95536d7c099ac9e65a93dca2d8413f041b04de2a6974c182ed68`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1941c3438b7f95536d7c099ac9e65a93dca2d8413f041b04de2a6974c182ed68`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1941c3438b7f95536d7c099ac9e65a93dca2d8413f041b04de2a6974c182ed68`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/std/core/dsl_spec.spl
mirror: doc/06_spec/unit/lib/std/core/dsl_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/core/dsl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/core/dsl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/core/dsl_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides context-aware building' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/core/dsl_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles undefined methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/core/dsl_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enables dynamic proxies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
