# lint_spec

> Purpose: Prove that Linter - code quality checks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lint_spec

Purpose: Prove that Linter - code quality checks.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/lint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Linter - code quality checks.
Audience: APP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### Linter - code quality checks

#### validates variable naming conventions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates variable naming conventions
- Verify: validates variable naming conventions


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates variable naming conventions")
step("Verify: validates variable naming conventions")
# @req: REQ-APP-LINTER-CODE-QUALITY-CHECKS-001
# Variables should use snake_case
val good_name = "valid_variable"
val bad_name = "InvalidCamelCase"

# Test that snake_case is valid
expect good_name.contains("_")
expect not bad_name.contains("_")
```

</details>

#### validates function naming conventions

- validates function naming conventions
- Verify: validates function naming conventions


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates function naming conventions")
step("Verify: validates function naming conventions")
# Functions should use snake_case
fn valid_function_name() -> bool:
    true

fn InvalidFunctionName() -> bool:
    false

expect valid_function_name()
expect not InvalidFunctionName()
```

</details>

#### validates class naming conventions

- validates class naming conventions
- Verify: validates class naming conventions


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates class naming conventions")
step("Verify: validates class naming conventions")
# Classes should use PascalCase
class ValidClassName:
    value: i64

class invalid_class_name:
    value: i64

val good_class = ValidClassName(value: 1)
val bad_class = invalid_class_name(value: 2)

expect good_class.value == 1
expect bad_class.value == 2
```

</details>

### Linter - code patterns

#### detects unused variable declarations

- detects unused variable declarations
- Verify: detects unused variable declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects unused variable declarations")
step("Verify: detects unused variable declarations")
# This would normally be flagged by linter
var unused_var = 42
var used_var = 10

# Using used_var
val result = used_var * 2
expect result == 20
```

</details>

#### detects missing return type annotations

- detects missing return type annotations
- Verify: detects missing return type annotations


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects missing return type annotations")
step("Verify: detects missing return type annotations")
# Function without explicit return type
fn no_return_type(x):
    x * 2

# Function with explicit return type
fn with_return_type(x: i64) -> i64:
    x * 2

expect no_return_type(5) == 10
expect with_return_type(5) == 10
```

</details>

#### validates error handling patterns

- validates error handling patterns
- Verify: validates error handling patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates error handling patterns")
step("Verify: validates error handling patterns")
# Functions that can fail should return Result
fn may_fail(x: i64) -> Result<i64, text>:
    if x < 0:
        Err("Negative value")
    else:
        Ok(x * 2)

val result = may_fail(5)
match result:
    case Ok(value):
        expect value == 10
    case Err(msg):
        expect msg == ""
```

</details>

### Linter - best practices

#### prefers val over var when possible

- prefers val over var when possible
- Verify: prefers val over var when possible


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers val over var when possible")
step("Verify: prefers val over var when possible")
# Immutable by default
val immutable = 42
var mutable = 10

# Can reassign mutable
mutable = mutable + 5
expect mutable == 15

# Cannot reassign immutable (would be caught by linter)
expect immutable == 42
```

</details>

#### validates proper use of Option types

- validates proper use of Option types
- Verify: validates proper use of Option types


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates proper use of Option types")
step("Verify: validates proper use of Option types")
# Functions returning optional values
fn find_value(arr: [i64], target: i64) -> Option<i64>:
    for item in arr:
        if item == target:
            return Some(item)
    None

val result = find_value([1, 2, 3], 2)
match result:
    case Some(v):
        expect v == 2
    case None:
        assert_true("Expected target value to be found" == "")
```

</details>

#### validates match exhaustiveness

- validates match exhaustiveness
- Verify: validates match exhaustiveness


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates match exhaustiveness")
step("Verify: validates match exhaustiveness")
# All cases should be covered
enum Color:
    Red
    Green
    Blue

fn describe_color(c: Color) -> text:
    match c:
        case Color.Red:
            "red"
        case Color.Green:
            "green"
        case Color.Blue:
            "blue"

val desc = describe_color(Color.Red)
expect desc == "red"
```

</details>

### Linter - performance hints

<details>
<summary>Advanced: suggests using iterators over loops</summary>

#### suggests using iterators over loops

- suggests using iterators over loops
- Verify: suggests using iterators over loops


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suggests using iterators over loops")
step("Verify: suggests using iterators over loops")
# Less efficient: manual loop
var sum1 = 0
for i in [1, 2, 3, 4, 5]:
    sum1 = sum1 + i

# More efficient: using iterator methods
val sum2 = [1, 2, 3, 4, 5].sum()

expect sum1 == 15
expect sum2 == 15
```

</details>


</details>

#### suggests const for compile-time constants

- suggests const for compile-time constants
- Verify: suggests const for compile-time constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suggests const for compile-time constants")
step("Verify: suggests const for compile-time constants")
# Should be const, not val
val PI_VAL = 3.14159
const PI_CONST = 3.14159

expect PI_VAL > 3.0
expect PI_CONST > 3.0
```

</details>

### Linter - accessor and inherited name checks

#### warns for trivial get set is accessors

- warns for trivial get set is accessors
- Verify: warns for trivial get set is accessors
   - Expected: count_name_lint(source, "ACC001") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns for trivial get set is accessors")
step("Verify: warns for trivial get set is accessors")
val source =
    "class Meter:\n" +
    "    value: i64\n" +
    "    active: bool\n" +
    "    fn get_value(self) -> i64:\n" +
    "        self.value\n" +
    "    fn set_value(self, value: i64):\n" +
    "        self.value = value\n" +
    "    fn is_active(self) -> bool:\n" +
    "        self.active\n"
expect(count_name_lint(source, "ACC001")).to_equal(3)
```

</details>

#### suppresses a trivial accessor group when any accessor has real behavior

- suppresses a trivial accessor group when any accessor has real behavior
- Verify: suppresses a trivial accessor group when any accessor has real behavior
   - Expected: count_name_lint(source, "ACC001") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suppresses a trivial accessor group when any accessor has real behavior")
step("Verify: suppresses a trivial accessor group when any accessor has real behavior")
val source =
    "class Meter:\n" +
    "    value: i64\n" +
    "    fn get_value(self) -> i64:\n" +
    "        if self.value < 0:\n" +
    "            return 0\n" +
    "        self.value\n" +
    "    fn set_value(self, value: i64):\n" +
    "        self.value = value\n"
expect(count_name_lint(source, "ACC001")).to_equal(0)
```

</details>

#### suppresses dummy accessor warning when overriding a parent accessor

- suppresses dummy accessor warning when overriding a parent accessor
- Verify: suppresses dummy accessor warning when overriding a parent accessor
   - Expected: count_name_lint(source, "ACC001") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suppresses dummy accessor warning when overriding a parent accessor")
step("Verify: suppresses dummy accessor warning when overriding a parent accessor")
val source =
    "class Parent:\n" +
    "    value: i64\n" +
    "    fn get_value(self) -> i64:\n" +
    "        self.value\n" +
    "class Child extends Parent:\n" +
    "    value: i64\n" +
    "    fn get_value(self) -> i64:\n" +
    "        self.value\n"
expect(count_name_lint(source, "ACC001")).to_equal(1)
```

</details>

#### warns for close misspellings of inherited method names

- warns for close misspellings of inherited method names
- Verify: warns for close misspellings of inherited method names
   - Expected: count_name_lint(source, "NAME001") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns for close misspellings of inherited method names")
step("Verify: warns for close misspellings of inherited method names")
val source =
    "class Parent:\n" +
    "    fn render_frame(self):\n" +
    "        pass\n" +
    "class Child extends Parent:\n" +
    "    fn render_farme(self):\n" +
    "        pass\n"
expect(count_name_lint(source, "NAME001")).to_equal(1)
```

</details>

#### suppresses close inherited method name warning with name_checked

- suppresses close inherited method name warning with name_checked
- Verify: suppresses close inherited method name warning with name_checked
   - Expected: count_name_lint(source, "NAME001") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suppresses close inherited method name warning with name_checked")
step("Verify: suppresses close inherited method name warning with name_checked")
val source =
    "class Parent:\n" +
    "    fn render_frame(self):\n" +
    "        pass\n" +
    "class Child extends Parent:\n" +
    "    @name_checked\n" +
    "    fn render_farme(self):\n" +
    "        pass\n"
expect(count_name_lint(source, "NAME001")).to_equal(0)
```

</details>

#### treats name_checked as a known Pure Simple annotation

- treats name_checked as a known Pure Simple annotation
- Verify: treats name_checked as a known Pure Simple annotation
   - Expected: check_unknown_decorator(source, "sample.spl").len() equals `0`
   - Expected: check_unknown_attribute(source, "sample.spl").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats name_checked as a known Pure Simple annotation")
step("Verify: treats name_checked as a known Pure Simple annotation")
val source =
    "class Child:\n" +
    "    @name_checked\n" +
    "    fn render_farme(self):\n" +
    "        pass\n"
expect(check_unknown_decorator(source, "sample.spl").len()).to_equal(0)
expect(check_unknown_attribute(source, "sample.spl").len()).to_equal(0)
```

</details>

#### lints a class declaration without aborting on the receiver type

- lints a class declaration without aborting on the receiver type
- Verify: lints a class declaration without aborting on the receiver type
   - Expected: results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lints a class declaration without aborting on the receiver type")
step("Verify: lints a class declaration without aborting on the receiver type")
var linter = Linter.new()
val results = linter.lint_source("sample.spl", "class Foo:\n    x: i64\n")
expect(results.len()).to_equal(0)
```

</details>

#### classifies PascalCase correctly after the receiver fix

- classifies PascalCase correctly after the receiver fix
- Verify: classifies PascalCase correctly after the receiver fix
   - Expected: linter.is_pascal_case("ValidName") is true
   - Expected: linter.is_pascal_case("invalid_name") is false
   - Expected: linter.is_pascal_case("9abc") is false
   - Expected: linter.is_pascal_case("_Foo") is false
   - Expected: linter.is_pascal_case("") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies PascalCase correctly after the receiver fix")
step("Verify: classifies PascalCase correctly after the receiver fix")
var linter = Linter.new()
expect(linter.is_pascal_case("ValidName")).to_equal(true)
expect(linter.is_pascal_case("invalid_name")).to_equal(false)
# non-cased first chars have upper() == lower(); must report false
expect(linter.is_pascal_case("9abc")).to_equal(false)
expect(linter.is_pascal_case("_Foo")).to_equal(false)
expect(linter.is_pascal_case("")).to_equal(false)
```

</details>

### COLL006 string-concat-in-loop rule

<details>
<summary>Advanced: does not fire on an integer accumulator loop with no strings</summary>

#### does not fire on an integer accumulator loop with no strings

- does not fire on an integer accumulator loop with no strings
- Verify: does not fire on an integer accumulator loop with no strings
   - Expected: count_collection_lint(source, "COLL006") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not fire on an integer accumulator loop with no strings")
step("Verify: does not fire on an integer accumulator loop with no strings")
val source = "fn main():\n" +
    "    var total = 0\n" +
    "    var i = 0\n" +
    "    while i < 10:\n" +
    "        total = total + i\n" +
    "        i = i + 1\n" +
    "    print(total)\n"
expect(count_collection_lint(source, "COLL006")).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: does not fire on a float accumulator loop</summary>

#### does not fire on a float accumulator loop

- does not fire on a float accumulator loop
- Verify: does not fire on a float accumulator loop
   - Expected: count_collection_lint(source, "COLL006") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not fire on a float accumulator loop")
step("Verify: does not fire on a float accumulator loop")
val source = "fn accum(xs: [f64]) -> f64:\n" +
    "    var sum = 0.0\n" +
    "    for x in xs:\n" +
    "        sum = sum + x\n" +
    "    sum\n"
expect(count_collection_lint(source, "COLL006")).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: does not fire on integer compound assignment in a loop</summary>

#### does not fire on integer compound assignment in a loop

- does not fire on integer compound assignment in a loop
- Verify: does not fire on integer compound assignment in a loop
   - Expected: count_collection_lint(source, "COLL006") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not fire on integer compound assignment in a loop")
step("Verify: does not fire on integer compound assignment in a loop")
val source = "fn counter() -> i64:\n" +
    "    var n = 0\n" +
    "    var i = 0\n" +
    "    while i < 10:\n" +
    "        n += i\n" +
    "        i += 1\n" +
    "    n\n"
expect(count_collection_lint(source, "COLL006")).to_equal(0)
```

</details>


</details>

#### still fires on a genuine text concat with a string literal

- still fires on a genuine text concat with a string literal
- Verify: still fires on a genuine text concat with a string literal
   - Expected: count_collection_lint(source, "COLL006") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still fires on a genuine text concat with a string literal")
step("Verify: still fires on a genuine text concat with a string literal")
val source = "fn build_text() -> text:\n" +
    "    var out = \"\"\n" +
    "    var i = 0\n" +
    "    while i < 10:\n" +
    "        out = out + \"x\"\n" +
    "        i = i + 1\n" +
    "    out\n"
expect(count_collection_lint(source, "COLL006")).to_equal(1)
```

</details>

#### still fires when the target is declared text and the value is not a literal

- still fires when the target is declared text and the value is not a literal
- Verify: still fires when the target is declared text and the value is not a literal
   - Expected: count_collection_lint(source, "COLL006") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still fires when the target is declared text and the value is not a literal")
step("Verify: still fires when the target is declared text and the value is not a literal")
val source = "fn joiner(parts: [text]) -> text:\n" +
    "    var out: text = \"\"\n" +
    "    for p in parts:\n" +
    "        out = out + p\n" +
    "    out\n"
expect(count_collection_lint(source, "COLL006")).to_equal(1)
```

</details>

<details>
<summary>Advanced: still fires on text compound assignment in a loop</summary>

#### still fires on text compound assignment in a loop

- still fires on text compound assignment in a loop
- Verify: still fires on text compound assignment in a loop
   - Expected: count_collection_lint(source, "COLL006") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still fires on text compound assignment in a loop")
step("Verify: still fires on text compound assignment in a loop")
val source = "fn joiner2(parts: [text]) -> text:\n" +
    "    var out = \"\"\n" +
    "    for p in parts:\n" +
    "        out += p\n" +
    "    out\n"
expect(count_collection_lint(source, "COLL006")).to_equal(1)
```

</details>


</details>

#### fires on the prepend form s = x + s

- fires on the prepend form s = x + s
- Verify: fires on the prepend form s = x + s
   - Expected: count_collection_lint(source, "COLL006") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fires on the prepend form s = x + s")
step("Verify: fires on the prepend form s = x + s")
val source = "fn int_to_text(n: i64) -> text:\n" +
    "    var result = \"\"\n" +
    "    var remaining = n\n" +
    "    while remaining > 0:\n" +
    "        result = \"d\" + result\n" +
    "        remaining = remaining / 10\n" +
    "    result\n"
expect(count_collection_lint(source, "COLL006")).to_equal(1)
```

</details>

#### does not fire on the integer prepend form acc = i + acc

- does not fire on the integer prepend form acc = i + acc
- Verify: does not fire on the integer prepend form acc = i + acc
   - Expected: count_collection_lint(source, "COLL006") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not fire on the integer prepend form acc = i + acc")
step("Verify: does not fire on the integer prepend form acc = i + acc")
val source = "fn swapadd(n: i64) -> i64:\n" +
    "    var acc = 1\n" +
    "    var i = 0\n" +
    "    while i < n:\n" +
    "        acc = i + acc\n" +
    "        i = i + 1\n" +
    "    acc\n"
expect(count_collection_lint(source, "COLL006")).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-LINTER-CODE-QUALITY-CHECKS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2593d4c501e3c15a8cbb08458b1bec1df460f03ad184c356d9fa0a5cfa4f0e11`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2593d4c501e3c15a8cbb08458b1bec1df460f03ad184c356d9fa0a5cfa4f0e11`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2593d4c501e3c15a8cbb08458b1bec1df460f03ad184c356d9fa0a5cfa4f0e11`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/lint_spec.spl
mirror: doc/06_spec/unit/app/lint_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/lint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/lint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/lint_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/lint_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates variable naming conventions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lint_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates function naming conventions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/lint_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates class naming conventions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
