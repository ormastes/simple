# Error Handling Specification

> Tests covering Result type, Option type, Try operator, Optional chaining, Null coalescing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Handling Specification

## Scenarios

### Result type

#### creates Ok result

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates Ok result


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Ok result")
val result: Result<i64, text> = Ok(42)
match result:
    case Ok(value):
        expect value == 42
    case Err(_):
        expect false
```

</details>

#### creates Err result

- creates Err result


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Err result")
val result: Result<i64, text> = Err("failed")
match result:
    case Err(msg):
        expect msg == "failed"
    case Ok(_):
        expect false
```

</details>

#### uses is_ok and is_err

- uses is_ok and is_err


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses is_ok and is_err")
val ok_result: Result<i64, text> = Ok(42)
val err_result: Result<i64, text> = Err("failed")

expect ok_result.is_ok()
expect not ok_result.is_err()
expect err_result.is_err()
expect not err_result.is_ok()
```

</details>

#### unwraps Ok values

- unwraps Ok values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwraps Ok values")
val result: Result<i64, text> = Ok(42)
val value = result.unwrap()
expect value == 42
```

</details>

#### provides default on error

- provides default on error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides default on error")
val result: Result<i64, text> = Err("failed")
val value = result.unwrap_or(0)
expect value == 0
```

</details>

#### maps Ok values

- maps Ok values


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Ok values")
val result: Result<i64, text> = Ok(10)
val doubled = result.map(_1 * 2)
match doubled:
    case Ok(value):
        expect value == 20
    case Err(_):
        expect false
```

</details>

#### maps Err values

- maps Err values


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Err values")
val result: Result<i64, text> = Err("error")
val mapped = result.map_err(&:upper)
match mapped:
    case Err(msg):
        expect msg == "ERROR"
    case Ok(_):
        expect false
```

</details>

### Option type

#### creates Some option

- creates Some option


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates Some option")
val opt: Option<i64> = Some(42)
match opt:
    case Some(value):
        expect value == 42
    case None:
        expect false
```

</details>

#### creates None option

- creates None option


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates None option")
val opt: Option<i64> = None
match opt:
    case None:
        expect true
    case Some(_):
        expect false
```

</details>

#### uses is_some and is_none

- uses is_some and is_none


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses is_some and is_none")
val some_val: Option<i64> = Some(42)
val none_val: Option<i64> = None

expect some_val.is_some()
expect not some_val.is_none()
expect none_val.is_none()
expect not none_val.is_some()
```

</details>

#### unwraps Some values

- unwraps Some values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwraps Some values")
val opt: Option<i64> = Some(42)
val value = opt.unwrap()
expect value == 42
```

</details>

#### provides default on None

- provides default on None


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides default on None")
val opt: Option<i64> = None
val value = opt.unwrap_or(0)
expect value == 0
```

</details>

#### maps Some values

- maps Some values


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps Some values")
val opt: Option<i64> = Some(10)
val doubled = opt.map(_1 * 2)
match doubled:
    case Some(value):
        expect value == 20
    case None:
        expect false
```

</details>

#### filters Some values

- filters Some values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters Some values")
val opt: Option<i64> = Some(10)
val filtered = opt.filter(_1 > 5)
expect filtered.is_some()

val rejected = opt.filter(_1 < 5)
expect rejected.is_none()
```

</details>

### Try operator

#### propagates errors with ?

- propagates errors with ?


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates errors with ?")
fn divide(a: i64, b: i64) -> Result<i64, text>:
    if b == 0:
        Err("Division by zero")
    else:
        Ok(a / b)

fn complex_calc(x: i64) -> Result<i64, text>:
    val step1 = divide(x, 2)?
    val step2 = divide(step1, 3)?
    Ok(step2)

val result = complex_calc(18)
match result:
    case Ok(value):
        expect value == 3  # 18/2/3 = 3
    case Err(_):
        expect false
```

</details>

#### short-circuits on first error

- short-circuits on first error


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("short-circuits on first error")
fn may_fail_early() -> Result<i64, text>:
    val x = Err("Early error")?
    Ok(x)

val result = may_fail_early()
match result:
    case Err(msg):
        expect msg == "Early error"
    case Ok(_):
        expect false
```

</details>

### Optional chaining

#### chains with ?. operator

- chains with ?. operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chains with ?. operator")
struct Address:
    city: text

struct Person:
    address: Option<Address>

val person = Person(address: Some(Address(city: "NYC")))
val city = person.address?.city
match city:
    case Some(c):
        expect c == "NYC"
    case None:
        expect false
```

</details>

#### returns None on any None in chain

- returns None on any None in chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns None on any None in chain")
struct Address:
    city: text

struct Person:
    address: Option<Address>

val person = Person(address: None)
val city = person.address?.city
expect city.is_none()
```

</details>

### Null coalescing

#### uses ?? for default values

- uses ?? for default values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses ?? for default values")
val maybe_value: Option<i64> = None
val value = maybe_value ?? 42
expect value == 42
```

</details>

#### returns value when Some

- returns value when Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns value when Some")
val maybe_value: Option<i64> = Some(10)
val value = maybe_value ?? 42
expect value == 10
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/error_handling_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Result type, Option type, Try operator, Optional chaining, Null coalescing.
- Result type
- Option type
- Try operator
- Optional chaining
- Null coalescing

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `816cc25511de9b886ac2ed1c9d1d32f99278eb57bf23a3d5ca77e95f3c501457`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `816cc25511de9b886ac2ed1c9d1d32f99278eb57bf23a3d5ca77e95f3c501457`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `816cc25511de9b886ac2ed1c9d1d32f99278eb57bf23a3d5ca77e95f3c501457`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/error_handling_spec.spl
mirror: doc/06_spec/01_unit/lib/common/error_handling_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/error_handling_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/error_handling_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/error_handling_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates Ok result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/error_handling_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates Err result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/error_handling_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses is_ok and is_err' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
