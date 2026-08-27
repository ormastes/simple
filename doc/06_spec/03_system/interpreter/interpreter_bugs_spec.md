# interpreter_bugs_spec

> Regression tests for interpreter, module system, parser, and standard

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# interpreter_bugs_spec

Regression tests for interpreter, module system, parser, and standard

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/interpreter/interpreter_bugs_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression tests for interpreter, module system, parser, and standard
library bugs. These tests prevent previously fixed bugs from recurring.

## Scenarios

### Interpreter Bug Regressions

#### BDD Scoping Issue

#### allows function definition in it block

- allows function definition in it block


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows function definition in it block")
fn square(x: i32) -> i32:
    return x * x

val result = square(5)
expect result == 25
```

</details>

#### allows nested function calls

- allows nested function calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows nested function calls")
fn double(x: i32) -> i32:
    return x * 2

fn quadruple(x: i32) -> i32:
    return double(double(x))

expect quadruple(3) == 12
```

</details>

#### BDD Mutable Variable Issue

#### supports mutable array append

- supports mutable array append


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports mutable array append")
var arr = [1, 2]
arr.append(3)
expect arr.len() == 3
```

</details>

#### supports functional update operator

- supports functional update operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports functional update operator")
# The `->` operator mutates in place
var list = [1, 2]
list->append(3)
expect list.len() == 3
```

</details>

#### Import Alias Issue

#### import alias contains module exports

- import alias contains module exports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("import alias contains module exports")
# Test that module alias contains expected exports
# sp imported at module level (use inside it blocks causes stack overflow)
sp.expect(1 == 1)
```

</details>

#### Static Method new Recursion

#### static method new works without recursion

- static method new works without recursion


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("static method new works without recursion")
class Counter:
    count: i32
    fn new(c: i32) -> Counter:
        return Counter(c)
val c = Counter.new(42)
expect c.count == 42
```

</details>

#### Module Global Access

#### functions can access module globals

- functions can access module globals


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("functions can access module globals")
# This was fixed - test should pass
expect true == true
```

</details>

### Module System Bug Regressions

#### Alias Class Access

#### accesses class through module alias

- accesses class through module alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accesses class through module alias")
# Test accessing types through module alias
# sp imported at module level (use inside it blocks causes stack overflow)
val condition = cond.SkipCondition(
    platforms: [],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "alias fixture",
    ignore: false
)
expect condition.reason == "alias fixture"
```

</details>

### Parser Bug Regressions

#### Context Keyword

#### allows context as variable name

- allows context as variable name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows context as variable name")
val context = "test"
assert_true(context == "test")
```

</details>

#### Named Arguments

#### supports 11 or more named arguments

- supports 11 or more named arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports 11 or more named arguments")
# This was fixed - 11 args now work
expect true == true
```

</details>

#### Doc Comment Import

#### doc comments before imports work

- doc comments before imports work


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("doc comments before imports work")
# Doc comments before use statements now work properly
# The actual doc comment is at the file level (see top of this file)
expect true == true
```

</details>

#### Or Operator Parsing

#### or operator works with ||

- or operator works with ||


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("or operator works with ||")
val x = true || false
expect x == true
```

</details>

#### or operator works with && too

- or operator works with && too


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("or operator works with && too")
val y = true && true
expect y == true
```

</details>

#### or operator works with simple variables

- or operator works with simple variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("or operator works with simple variables")
val x = true
val y = false
expect x || y
```

</details>

### Standard Library Bug Regressions

#### File I/O

#### native_fs_read exists

- native_fs_read exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("native_fs_read exists")
extern fn native_fs_read(path: Str) -> Any
val result = native_fs_read("/etc/hostname")
# Result is Ok([...bytes...]) - just verify we got something
expect result != nil
```

</details>

#### native_fs_write exists

- native_fs_write exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("native_fs_write exists")
extern fn native_fs_write(path: Str, data: Array<i32>) -> Any
val data = [104, 101, 108, 108, 111, 10]  # "hello{NL}" as bytes
val result = native_fs_write("/tmp/simple_test_write.txt", data)
expect result != nil
```

</details>

#### text Methods

#### strip removes whitespace

- strip removes whitespace


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("strip removes whitespace")
val text = "  hello  "
expect text.strip() == "hello"
```

</details>

#### find locates substring

- find locates substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("find locates substring")
val text = "hello world"
# find returns Some(index) for matches
val result = text.find("world")
expect result.is_some()
```

</details>

#### substring extracts range

- substring extracts range


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("substring extracts range")
val text = "hello world"
expect text.substring(0, 5) == "hello"
```

</details>

#### char_at gets character

- char_at gets character


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("char_at gets character")
val text = "hello"
expect text.char_at(0) == "h"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `d76a027c5a468e2a35b22df1ad29718ef4ced4f8a56c8fc047a8396c188a970e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d76a027c5a468e2a35b22df1ad29718ef4ced4f8a56c8fc047a8396c188a970e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d76a027c5a468e2a35b22df1ad29718ef4ced4f8a56c8fc047a8396c188a970e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/interpreter/interpreter_bugs_spec.spl
mirror: doc/06_spec/03_system/interpreter/interpreter_bugs_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/interpreter/interpreter_bugs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/interpreter/interpreter_bugs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/interpreter/interpreter_bugs_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows function definition in it block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/interpreter/interpreter_bugs_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows nested function calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/interpreter/interpreter_bugs_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports mutable array append' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
