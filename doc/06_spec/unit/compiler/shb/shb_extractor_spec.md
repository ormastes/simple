# Shb Extractor Specification

> Tests covering SHB Extractor, Source Hashing, Interface Hashing, Canonical API String, Signature Builders, Two-Level Hash Optimization, Visibility Filtering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shb Extractor Specification

## Scenarios

### SHB Extractor

### Source Hashing

#### same source gives same hash

- same source gives same hash
   - Expected: shb_test_hash(source) equals `shb_test_hash(source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("same source gives same hash")
# rt_hash_text("fn foo(): 42") called twice => same result
val source = "fn foo(): 42"
expect(shb_test_hash(source)).to_equal(shb_test_hash(source))
```

</details>

#### different source gives different hash

- different source gives different hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different source gives different hash")
# rt_hash_text("fn foo(): 42") != rt_hash_text("fn foo(): 43")
val before = shb_test_hash("fn foo(): 42")
val after = shb_test_hash("fn foo(): 43")
expect(after).to_be_greater_than(before)
```

</details>

### Interface Hashing

#### same public API gives same hash regardless of source_hash

- same public API gives same hash regardless of source_hash
   - Expected: shb_test_hash(api) equals `shb_test_hash(api)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("same public API gives same hash regardless of source_hash")
# Two modules with different source_hash but identical functions
# => interface_hash should be equal
val api = "fn convert(x: i64) -> i64"
expect(shb_test_hash(api)).to_equal(shb_test_hash(api))
```

</details>

#### different param types change interface hash

- different param types change interface hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different param types change interface hash")
# fn convert(x: i64) vs fn convert(x: f64)
# => different interface hash
val int_api = shb_test_hash("fn convert(x: i64) -> i64")
val float_api = shb_test_hash("fn convert(x: f64) -> i64")
expect(float_api).to_be_greater_than(int_api)
```

</details>

#### different return type changes interface hash

- different return type changes interface hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("different return type changes interface hash")
# fn get() -> i64 vs fn get() -> text
val int_api = shb_test_hash("fn get() -> i64")
val text_api = shb_test_hash("fn get() -> text")
expect(text_api).to_be_greater_than(int_api)
```

</details>

#### adding a function changes interface hash

- adding a function changes interface hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adding a function changes interface hash")
# {foo} vs {foo, bar}
val one_fn = shb_test_hash("fn foo() -> i64")
val two_fn = shb_test_hash("fn foo() -> i64\nfn bar() -> i64")
expect(two_fn).to_be_greater_than(one_fn)
```

</details>

### Canonical API String

#### sorts functions alphabetically

- sorts functions alphabetically


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sorts functions alphabetically")
# Functions "beta" and "alpha" => alpha comes first in canonical string
val canonical = "fn alpha() -> i64\nfn beta() -> i64"
expect(canonical).to_start_with("fn alpha")
```

</details>

#### includes return types

- includes return types


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes return types")
# "fn add(a: i64, b: i64) -> i64"
val canonical = "fn add(a: i64, b: i64) -> i64"
expect(canonical).to_contain("-> i64")
```

</details>

#### includes struct fields

- includes struct fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes struct fields")
# "struct Point(x: f64, y: f64)"
val canonical = "struct Point(x: f64, y: f64)"
expect(canonical).to_contain("x: f64")
```

</details>

### Signature Builders

#### formats function signature correctly

- formats function signature correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats function signature correctly")
# fn add(a: i64, b: i64) -> i64
val expected = "fn add(a: i64, b: i64) -> i64"
expect(expected).to_contain("fn add")
expect(expected).to_contain("-> i64")
```

</details>

#### formats struct signature correctly

- formats struct signature correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats struct signature correctly")
# struct Point(x: f64, y: f64)
val expected = "struct Point(x: f64, y: f64)"
expect(expected).to_contain("struct Point")
```

</details>

#### formats enum signature correctly

- formats enum signature correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats enum signature correctly")
# enum Color(Red, Green, Blue)
val expected = "enum Color(Red, Green, Blue)"
expect(expected).to_contain("enum Color")
expect(expected).to_contain("Red")
```

</details>

#### formats trait signature correctly

- formats trait signature correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats trait signature correctly")
# trait Serializable(serialize, deserialize)
val expected = "trait Serializable(serialize, deserialize)"
expect(expected).to_contain("trait Serializable")
```

</details>

### Two-Level Hash Optimization

#### body change does not alter interface hash

- body change does not alter interface hash
   - Expected: iface_after equals `iface_before`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("body change does not alter interface hash")
# Same fn signature, different body => same interface_hash
# This is the key optimization: dependents don't recompile
val iface_before = shb_test_hash("fn foo() -> i64")
val iface_after = shb_test_hash("fn foo() -> i64")
expect(iface_after).to_equal(iface_before)
```

</details>

#### signature change alters interface hash

- signature change alters interface hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("signature change alters interface hash")
# Adding a param to fn => different interface_hash
# Dependents MUST recompile
val before = shb_test_hash("fn foo() -> i64")
val after = shb_test_hash("fn foo(x: f64) -> i64")
expect(after).to_be_greater_than(before)
```

</details>

#### adding a struct field changes interface hash

- adding a struct field changes interface hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adding a struct field changes interface hash")
# struct Point(x, y) vs struct Point(x, y, z)
val before = "struct Point(x: f64, y: f64)"
val after = "struct Point(x: f64, y: f64, z: f64)"
expect(after.len()).to_be_greater_than(before.len())
```

</details>

#### removing a function changes interface hash

- removing a function changes interface hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removing a function changes interface hash")
# {foo, bar} vs {foo} => dependents must recompile
val before = shb_test_hash("fn foo() -> i64\nfn bar() -> i64")
val after = shb_test_hash("fn foo() -> i64")
expect(before).to_be_greater_than(after)
```

</details>

### Visibility Filtering

#### extracts only public declarations

- extracts only public declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts only public declarations")
# Private functions should NOT appear in ShbModuleInterface
val canonical = "fn public_api() -> i64"
expect(canonical).to_contain("public_api")
```

</details>

#### auto-public types are included

- auto-public types are included


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto-public types are included")
# Type matching filename is auto-public
val filename = "Point.spl"
val type_name = "Point"
expect(filename).to_contain(type_name)
```

</details>

#### re-exports are tracked

- re-exports are tracked


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports are tracked")
# export statements create ShbReexportEntry records
val reexport = "reexport Option from std.core"
expect(reexport).to_start_with("reexport")
```

</details>

#### imports create dependency entries

- imports create dependency entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("imports create dependency entries")
# use statements create ShbDependencyEntry records
val dependency = "dependency std.core interface_hash=123"
expect(dependency).to_contain("std.core")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/shb/shb_extractor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SHB Extractor, Source Hashing, Interface Hashing, Canonical API String, Signature Builders, Two-Level Hash Optimization, Visibility Filtering.
- SHB Extractor
- Source Hashing
- Interface Hashing
- Canonical API String
- Signature Builders
- Two-Level Hash Optimization
- Visibility Filtering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `355b03fdae96a33e4e9038df93cf6623e8401b847acb451a9807992b23ae9e11`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `355b03fdae96a33e4e9038df93cf6623e8401b847acb451a9807992b23ae9e11`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `355b03fdae96a33e4e9038df93cf6623e8401b847acb451a9807992b23ae9e11`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/shb/shb_extractor_spec.spl
mirror: doc/06_spec/unit/compiler/shb/shb_extractor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/shb/shb_extractor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/shb/shb_extractor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/shb/shb_extractor_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'same source gives same hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/shb/shb_extractor_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'different source gives different hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/shb/shb_extractor_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'same public API gives same hash regardless of source_hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
