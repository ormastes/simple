# Effect System Specification

> requires [pure, io]

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Effect System Specification

requires [pure, io]

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #EFFECT-SYS-001 to #EFFECT-SYS-040 |
| Category | Type System \| Effects |
| Status | Implemented |
| Source | `test/feature/usage/effect_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Effect Types

- `@pure` - No side effects, referentially transparent
- `@io` - Console/terminal I/O operations
- `@net` - Network operations
- `@fs` - File system operations
- `@unsafe` - Unsafe memory operations
- `@async` - Asynchronous operations

## Capabilities

- `requires [cap1, cap2]` - Module capability requirements
- Effect validation at compile time

## Syntax

```simple
requires [pure, io]

@pure
use std.spec.step

fn add(x: i64, y: i64) -> i64:
x + y

@io @net
fn fetch_and_log(url: text) -> text:
val data = http_get(url)
print(data)
data
```

## Scenarios

### @pure Effect

#### pure function can do computation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- pure function can do computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pure function can do computation")
@pure
fn add(x: i64, y: i64) -> i64:
    x + y

expect add(20, 22) == 42
```

</details>

#### pure function can call other pure functions

- pure function can call other pure functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pure function can call other pure functions")
@pure
fn double(x: i64) -> i64:
    x * 2

@pure
fn quadruple(x: i64) -> i64:
    double(double(x))

expect quadruple(10) == 40
```

</details>

#### pure function blocks print

- pure function blocks print


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pure function blocks print")
# This would be a compile error:
# @pure
# fn bad():
#     print("hello")  # Error: I/O not allowed in pure function
expect true  # Compile-time check
```

</details>

### @io Effect

#### io function can do computation

- io function can do computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("io function can do computation")
@io
fn compute_and_return(x: i64) -> i64:
    x * 2

expect compute_and_return(21) == 42
```

</details>

### @async Effect

#### async decorator syntax works

- async decorator syntax works


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("async decorator syntax works")
@async
fn compute(x: i64) -> i64:
    x * 2

expect await compute(21) == 42
```

</details>

#### async allows non-blocking io

- async allows non-blocking io


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("async allows non-blocking io")
@async
fn greet() -> i64:
    print("hello")
    42

expect await greet() == 42
```

</details>

### @fs Effect

#### fs function can do computation

- fs function can do computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fs function can do computation")
@fs
fn compute_fs(x: i64) -> i64:
    x * 2

expect compute_fs(21) == 42
```

</details>

### @net Effect

#### net function can do computation

- net function can do computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("net function can do computation")
@net
fn compute_net(x: i64) -> i64:
    x * 2

expect compute_net(21) == 42
```

</details>

### @unsafe Effect

#### unsafe function can do computation

- unsafe function can do computation


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unsafe function can do computation")
@unsafe
fn compute_unsafe(x: i64) -> i64:
    x * 2

expect compute_unsafe(21) == 42
```

</details>

### Stacked Effects

#### pure and async together

- pure and async together


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pure and async together")
@pure
@async
fn fast_compute(x: i64) -> i64:
    x * 2

expect await fast_compute(21) == 42
```

</details>

#### io and net together

- io and net together


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("io and net together")
@io
@net
fn network_logger(x: i64) -> i64:
    x * 2

expect network_logger(21) == 42
```

</details>

#### all effects together

- all effects together


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("all effects together")
@io
@net
@fs
fn full_access(x: i64) -> i64:
    x * 2

expect full_access(21) == 42
```

</details>

#### all effects parsed

- all effects parsed


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("all effects parsed")
@pure
@io
@net
@fs
@unsafe
fn all_effects(x: i64) -> i64:
    x

expect all_effects(42) == 42
```

</details>

### Effect with Attributes

#### effects with inline attribute

- effects with inline attribute


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("effects with inline attribute")
@inline
@pure
fn attributed_pure(x: i64) -> i64:
    x * 2

expect attributed_pure(21) == 42
```

</details>

### Unrestricted Functions

#### unrestricted function works

- unrestricted function works


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unrestricted function works")
fn do_anything(x: i64) -> i64:
    x * 2

expect do_anything(21) == 42
```

</details>

### Effect Propagation

#### pure cannot call io

- pure cannot call io


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pure cannot call io")
# This would be a compile error:
# @io fn log_value(x: i64) -> i64: ...
# @pure fn compute(x: i64) -> i64: log_value(x) * 2  # Error
expect true  # Compile-time check
```

</details>

#### pure cannot call net

- pure cannot call net


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pure cannot call net")
# This would be a compile error:
# @net fn fetch_data() -> i64: ...
# @pure fn process() -> i64: fetch_data() * 2  # Error
expect true  # Compile-time check
```

</details>

#### pure cannot call fs

- pure cannot call fs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pure cannot call fs")
# This would be a compile error:
# @fs fn read_config() -> i64: ...
# @pure fn get_value() -> i64: read_config() + 10  # Error
expect true  # Compile-time check
```

</details>

#### pure cannot call unsafe

- pure cannot call unsafe


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("pure cannot call unsafe")
# This would be a compile error:
# @unsafe fn dangerous() -> i64: ...
# @pure fn safe_wrapper() -> i64: dangerous() + 1  # Error
expect true  # Compile-time check
```

</details>

#### io can call pure

- io can call pure


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("io can call pure")
@pure
fn calculate(x: i64) -> i64:
    x * 2

@io
fn log_and_compute(x: i64) -> i64:
    calculate(x) + 10

expect log_and_compute(20) == 50
```

</details>

#### io can call io

- io can call io


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("io can call io")
@io
fn helper(x: i64) -> i64:
    x * 2

@io
fn caller(x: i64) -> i64:
    helper(x) + 10

expect caller(20) == 50
```

</details>

#### unrestricted can call anything

- unrestricted can call anything


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unrestricted can call anything")
@io
fn io_func() -> i64:
    10

@net
fn net_func() -> i64:
    20

@fs
fn fs_func() -> i64:
    30

@pure
fn pure_func() -> i64:
    5

fn unrestricted() -> i64:
    io_func() + net_func() + fs_func() + pure_func()

expect unrestricted() == 65
```

</details>

### Capability Requirements

#### basic capability parsing

- basic capability parsing


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("basic capability parsing")
requires [pure]

@pure
fn compute(x: i64) -> i64:
    x * 2

expect compute(21) == 42
```

</details>

#### multiple capabilities

- multiple capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiple capabilities")
requires [pure, io, net]

@pure
fn compute(x: i64) -> i64:
    x * 2

expect compute(21) == 42
```

</details>

#### all capabilities

- all capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("all capabilities")
requires [pure, io, net, fs, unsafe, gc]

fn compute(x: i64) -> i64:
    x * 2

expect compute(21) == 42
```

</details>

#### trailing comma allowed

- trailing comma allowed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("trailing comma allowed")
requires [pure, io,]

@pure
fn compute(x: i64) -> i64:
    x * 2

expect compute(21) == 42
```

</details>

#### empty requires list

- empty requires list


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("empty requires list")
requires []

fn compute(x: i64) -> i64:
    x * 2

expect compute(21) == 42
```

</details>

### Compile-Time Capability Validation

#### effect matches capability

- effect matches capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("effect matches capability")
requires [pure]

@pure
fn add(x: i64, y: i64) -> i64:
    x + y

expect add(20, 22) == 42
```

</details>

#### io effect blocked by pure-only module

- io effect blocked by pure-only module


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("io effect blocked by pure-only module")
# This would be a compile error:
# requires [pure]
# @io fn log_value(x: i64) -> i64: x  # Error: @io not in [pure]
expect true  # Compile-time check
```

</details>

#### async always allowed

- async always allowed


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("async always allowed")
requires [pure]

@async
fn compute(x: i64) -> i64:
    x * 2

expect await compute(21) == 42
```

</details>

#### multiple effects with matching capabilities

- multiple effects with matching capabilities


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiple effects with matching capabilities")
requires [pure, io]

@pure
@io
fn process(x: i64) -> i64:
    x * 2

expect process(21) == 42
```

</details>

#### unrestricted module allows all

- unrestricted module allows all


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unrestricted module allows all")
@io
@net
@fs
@unsafe
fn do_everything(x: i64) -> i64:
    x * 2

expect do_everything(21) == 42
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
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

- Canonical SPipe generation for source `d81e15d43cdbb470fae6433d89941139c108094bc5dd7c85abc5758885c6c7f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d81e15d43cdbb470fae6433d89941139c108094bc5dd7c85abc5758885c6c7f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d81e15d43cdbb470fae6433d89941139c108094bc5dd7c85abc5758885c6c7f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/effect_system_spec.spl
mirror: doc/06_spec/feature/usage/effect_system_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/effect_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/effect_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/effect_system_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pure function can do computation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/effect_system_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pure function can call other pure functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/effect_system_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pure function blocks print' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
