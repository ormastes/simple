# Unnamed Duplicate Typed Arguments Warning Specification

> This lint warns when a function has multiple parameters of the same type that

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unnamed Duplicate Typed Arguments Warning Specification

This lint warns when a function has multiple parameters of the same type that

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LINT-001 |
| Category | Lint |
| Status | Implemented |
| Source | `test/03_system/feature/usage/unnamed_duplicate_typed_args_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This lint warns when a function has multiple parameters of the same type that
are passed positionally without named arguments. This helps prevent argument
order mistakes at call sites by encouraging explicit naming.

## Scenarios

### Unnamed Duplicate Typed Args Warning

#### functions with duplicate typed params

#### warns on positional call with two text params

- warns on positional call with two text params


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("warns on positional call with two text params")
# When a function has fn foo(a: text, b: text)
# calling foo(x, y) should warn, but foo(a=x, b=y) should not
fn copy_text(src: text, dest: text) -> text:
    dest

# Named arguments - no warning
val result = copy_text(src="source", dest="destination")
expect result == "destination"
```

</details>

#### accepts named arguments without warning

- accepts named arguments without warning


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts named arguments without warning")
fn swap(left: i64, right: i64) -> (i64, i64):
    (right, left)

# Named call prevents accidental swapping
val (a, b) = swap(left=1, right=2)
expect a == 2
expect b == 1
```

</details>

#### works with mixed named and positional args

- works with mixed named and positional args


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("works with mixed named and positional args")
fn range_check(value: i64, min: i64, max: i64) -> bool:
    value >= min && value <= max

# First positional, rest named
val ok = range_check(5, min=0, max=10)
expect ok == true
```

</details>

#### no warning cases

#### does not warn on single parameter

- does not warn on single parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not warn on single parameter")
fn single(x: text) -> text:
    x
expect single("hello") == "hello"
```

</details>

#### does not warn on different typed params

- does not warn on different typed params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not warn on different typed params")
fn mixed(name: text, count: i64) -> text:
    "{name}: {count}"
expect mixed("items", 5) == "items: 5"
```

</details>

#### does not warn when all params are named

- does not warn when all params are named


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not warn when all params are named")
fn coords(x: i64, y: i64, z: i64) -> i64:
    x + y + z
expect coords(x=1, y=2, z=3) == 6
```

</details>

#### real world examples

#### copy function with named args

- copy function with named args


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("copy function with named args")
fn copy_file(source: text, dest: text) -> text:
    "Copied {source} to {dest}"

# Using named args prevents confusing source/dest
val msg = copy_file(source="/a/b.txt", dest="/c/d.txt")
expect msg == "Copied /a/b.txt to /c/d.txt"
```

</details>

#### compare function with named args

- compare function with named args


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compare function with named args")
fn compare(expected: text, actual: text) -> bool:
    expected == actual

# Named args clarify which is expected vs actual
expect compare(expected="hello", actual="hello") == true
```

</details>

#### move function with named args

- move function with named args


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("move function with named args")
fn move_item(from_pos: i64, to_pos: i64) -> i64:
    to_pos - from_pos

# Clear intent with named args
val distance = move_item(from_pos=0, to_pos=10)
expect distance == 10
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `ec3cbbb92e5dac6f0d904b8941002a762e85d46b4b8aae1ee799a57cd29d896a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec3cbbb92e5dac6f0d904b8941002a762e85d46b4b8aae1ee799a57cd29d896a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec3cbbb92e5dac6f0d904b8941002a762e85d46b4b8aae1ee799a57cd29d896a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/unnamed_duplicate_typed_args_spec.spl
mirror: doc/06_spec/03_system/feature/usage/unnamed_duplicate_typed_args_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/unnamed_duplicate_typed_args_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/unnamed_duplicate_typed_args_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/unnamed_duplicate_typed_args_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns on positional call with two text params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/unnamed_duplicate_typed_args_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts named arguments without warning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/unnamed_duplicate_typed_args_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works with mixed named and positional args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
