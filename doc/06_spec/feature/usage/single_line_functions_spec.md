# Single-Line Function Definitions Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Single-Line Function Definitions Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SYNTAX-INLINE |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/single_line_functions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
use std.spec.step

fn name(): implicit_return_expr
fn name(param: Type) -> ReturnType: expr
```

## Key Behaviors

- Single-line functions have an implicit return expression (no explicit `return` needed)
- The expression is evaluated and returned automatically
- Explicit return types are optional but supported
- Works with zero, one, or multiple parameters
- Compatible with class methods and static functions
- Traditional block syntax is still supported and can be mixed in the same file

## Scenarios

### Single-Line Function Definitions

#### basic syntax

#### parses inline expression body

- parses inline expression body


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses inline expression body")
fn double(x): x * 2
expect double(5) == 10
```

</details>

#### parses with multiple parameters

- parses with multiple parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses with multiple parameters")
fn add(a, b): a + b
expect add(3, 4) == 7
```

</details>

#### parses with no parameters

- parses with no parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses with no parameters")
fn get_answer(): 42
expect get_answer() == 42
```

</details>

#### handles complex expressions

- handles complex expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles complex expressions")
fn complex(x): (x * 2) + (x / 2)
expect complex(10) == 25
```

</details>

#### returns immediately without explicit return

- returns immediately without explicit return


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns immediately without explicit return")
fn square(x): x * x
expect square(4) == 16
```

</details>

#### with explicit return types

#### supports explicit return type annotation

- supports explicit return type annotation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports explicit return type annotation")
fn typed_double(x: i64) -> i64: x * 2
expect typed_double(5) == 10
```

</details>

#### works with function parameter types

- works with function parameter types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with function parameter types")
fn typed_add(a: i64, b: i64) -> i64: a + b
expect typed_add(10, 20) == 30
```

</details>

#### infers return type from expression

- infers return type from expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("infers return type from expression")
fn inferred(x): x + 1
expect inferred(41) == 42
```

</details>

#### with method definitions

#### works with class methods

- works with class methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with class methods")
class Counter:
    count: i64

    fn get_count(): self.count

val c = Counter(count: 42)
expect c.get_count() == 42
```

</details>

#### works with mutable methods

- works with mutable methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with mutable methods")
class Accumulator:
    total: i64

    me add(value: i64):
        self.total = self.total + value

val acc = Accumulator(total: 0)
acc.add(5)
acc.add(10)
expect acc.total == 15
```

</details>

#### works with static functions

- works with static functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with static functions")
class MathHelper:
    static fn pi_approximation(): 3.14159

expect MathHelper.pi_approximation() == 3.14159
```

</details>

#### with collection operations

#### works with lambda-like expressions

- works with lambda-like expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with lambda-like expressions")
fn twice_each(items: List<i64>): items.map(_ * 2)
expect twice_each([1, 2, 3]) == [2, 4, 6]
```

</details>

#### handles filtering in single line

- handles filtering in single line


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles filtering in single line")
fn evens_only(items: List<i64>): items.filter(_ % 2 == 0)
expect evens_only([1, 2, 3, 4, 5]) == [2, 4]
```

</details>

#### mixing with block syntax

#### can coexist with traditional block functions

- can coexist with traditional block functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("can coexist with traditional block functions")
fn inline(x): x * 2
fn block(x):
    val doubled = inline(x)
    doubled + 1
expect block(5) == 11
```

</details>

#### block functions still work normally

- block functions still work normally


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("block functions still work normally")
fn block_complex(x):
    val y = x * 2
    y + 1
expect block_complex(5) == 11
```

</details>

#### allows either style in same module

- allows either style in same module


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allows either style in same module")
fn style1(x): x + 1
fn style2(x):
    x + 2
expect style1(10) == 11
expect style2(10) == 12
```

</details>

#### edge cases

#### works with nested function calls

- works with nested function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with nested function calls")
fn inner(x): x + 1
fn outer(x):
    inner(x * 2)
expect outer(5) == 11
```

</details>

#### handles string expressions

- handles string expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles string expressions")
fn greeting(name): "Hello, {name}!"
expect greeting("World") == "Hello, World!"
```

</details>

#### works with conditional expressions

- works with conditional expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with conditional expressions")
fn max_of_two(a, b): if a > b: a else: b
expect max_of_two(10, 5) == 10
expect max_of_two(3, 8) == 8
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `51c23afc3cd5e4616ec8d3018ec0adb0450bc51e049c73f1ea1fedfe198b3a03`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `51c23afc3cd5e4616ec8d3018ec0adb0450bc51e049c73f1ea1fedfe198b3a03`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `51c23afc3cd5e4616ec8d3018ec0adb0450bc51e049c73f1ea1fedfe198b3a03`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/feature/usage/single_line_functions_spec.spl
mirror: doc/06_spec/feature/usage/single_line_functions_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/single_line_functions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/single_line_functions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/single_line_functions_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses inline expression body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/single_line_functions_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses with multiple parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/single_line_functions_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses with no parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/single_line_functions_spec.spl:142:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can coexist with traditional block functions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
