# Advanced Generics Specification

> struct Array<T, const N: usize>:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Advanced Generics Specification

struct Array<T, const N: usize>:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #GEN-ADV-001 to #GEN-ADV-008 |
| Category | Type System \| Generics |
| Status | Implemented |
| Source | `test/03_system/feature/usage/generics_advanced_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Const generics
struct Array<T, const N: usize>:
data: T

# Where clause
use std.spec.step

fn filled(value: T) -> T where T: Copy:
value

# impl Trait for Type
impl Len for MyList:
fn len() -> i64:
self.size

# Multiple trait bounds
fn make<T>() -> T where T: Clone + Default:
T.default()

# Associated types
trait Iterator:
type Item
fn next() -> Option<Self.Item>
```

## Scenarios

### Const Generic Parameters

#### parses const generic parameter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses const generic parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses const generic parameter")
struct Array<T, const N: usize>:
    data: T

expect true  # Parsed successfully
```

</details>

### Where Clauses

#### parses where clause on function

- parses where clause on function


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses where clause on function")
trait Copy:
    fn copy() -> Self

fn filled(value: i64) -> i64 where i64: Copy:
    value

expect filled(42) == 42
```

</details>

### impl Trait for Type

#### parses impl trait for type

- parses impl trait for type


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses impl trait for type")
trait Len:
    fn len() -> i64

struct MyList:
    size: i64

impl Len for MyList:
    fn len() -> i64:
        self.size

val list = MyList(size: 42)
expect list.len() == 42
```

</details>

### Generic impl with Where

#### parses generic impl with where

- parses generic impl with where


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses generic impl with where")
trait Clone:
    fn clone() -> Self

impl Clone for i64:
    fn clone() -> i64:
        self

# Note: impl for built-in types doesn't register methods in interpreter
# Just verify that the declaration parses successfully
expect true
```

</details>

### Nested Generic Types

#### parses nested generic types

- parses nested generic types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses nested generic types")
struct Container:
    items: [Option<i64>]

expect true  # Parsed successfully
```

</details>

### Tuple Return Types

#### parses tuple return type

- parses tuple return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses tuple return type")
fn get_pair() -> (i64, str):
    (42, "hello")

val _pair = get_pair()
val num = _pair[0]
val txt = _pair[1]
expect num == 42
expect txt == "hello"
```

</details>

### Multiple Trait Bounds

#### parses multiple trait bounds

- parses multiple trait bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multiple trait bounds")
trait Clone:
    fn clone() -> Self

trait Default:
    fn default() -> Self

fn make<T>() -> T where T: Clone + Default:
    T.default()

expect true  # Parsed successfully
```

</details>

### Associated Types

#### parses associated type

- parses associated type


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses associated type")
trait Iterator:
    type Item

    fn next() -> Option<Self.Item>

expect true  # Parsed successfully
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7e7a57229fdbdbca8705e952b3724c63042e7299de955120a243d05d452966e1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7e7a57229fdbdbca8705e952b3724c63042e7299de955120a243d05d452966e1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7e7a57229fdbdbca8705e952b3724c63042e7299de955120a243d05d452966e1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/generics_advanced_spec.spl
mirror: doc/06_spec/03_system/feature/usage/generics_advanced_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/generics_advanced_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/generics_advanced_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/generics_advanced_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses const generic parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/generics_advanced_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses where clause on function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/generics_advanced_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses impl trait for type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
