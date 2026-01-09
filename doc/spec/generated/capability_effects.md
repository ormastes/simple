# Capability-Based Effects Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/capability_effects_spec.spl`
> **Generated:** 2026-01-09 06:34:16
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/capability_effects_spec.spl
> ```

**Status:** 📋 Planned
**Feature IDs:** #880-884
**Keywords:** effects, capabilities, purity, safety, LLM-safety
**Last Updated:** 2026-01-09
**Topics:** effects, type-system, safety
**Symbols:** Effect, Capability, Pure, IO, Net, FS, EffectChecker
**Module:** simple_compiler::effects
**LLM Safety:** Prevent accidental side effects in AI-generated code
**Explicit Effects:** All effects visible in signatures and modules
**Compile-Time Checking:** Effect violations caught at compile time
**Fine-Grained Control:** Granular capability requirements

## Quick Navigation

- [Overview](#overview)
- [Symbols Reference](#symbols-reference)
- [Test Cases](#test-cases) (14 tests)
- [Source Code](#source-code)

## Overview

Capability-based effect system that prevents LLMs from silently adding I/O or stateful behavior to pure code. Explicit effect markers (`@pure`, `@io`, `@net`, `@fs`) make side effects visible and checked at compile time.

## Related Specifications

- **Type System** - Effect type annotations
- **Module System** - Capability requirements
- **Functions** - Effect propagation and checking

---

## Symbols Reference

| Symbol | Used in Tests |
|--------|---------------|
| `Add` | [4](#auto_inferred), [5](#add) |
| `Auto` | [4](#auto_inferred) |
| `AutoInferred` | [4](#auto_inferred) |
| `Calculate` | [2](#calculate), [3](#calculate_tax), [9](#calculate), [13](#calculate_discount) |
| `CalculateDiscount` | [13](#calculate_discount) |
| `CalculateTax` | [3](#calculate_tax) |
| `Can` | [1](#features_1), [7](#unnamed_test) |
| `Cannot` | [7](#unnamed_test) |
| `Capability` | [1](#features_1) |
| `Compiler` | [1](#features_1), [4](#auto_inferred) |
| `Deterministic` | [12](#println) |
| `Discount` | [13](#calculate_discount) |
| `Done` | [7](#unnamed_test) |
| `Double` | [6](#double) |
| `E0420` | [9](#calculate) |
| `E0421` | [10](#pure_func) |
| `E0422` | [11](#features_11) |
| `ERROR` | [1](#features_1), [3](#calculate_tax), [5](#add), [6](#double), [7](#unnamed_test), ... (9 total) |
| `Effect` | [1](#features_1), [8](#unnamed_test) |
| `Error` | [9](#calculate), [10](#pure_func), [11](#features_11) |
| `Features` | [1](#features_1), [11](#features_11) |
| `Func` | [10](#pure_func) |
| `Function` | [4](#auto_inferred) |
| `Handle` | [14](#handle_request) |
| `HandleRequest` | [14](#handle_request) |
| `Impure` | [6](#double) |
| `Inferred` | [4](#auto_inferred), [8](#unnamed_test) |
| `LLM` | [13](#calculate_discount) |
| `Links` | [1](#features_1) |
| `Module` | [1](#features_1), [2](#calculate) |
| `Multiple` | [3](#calculate_tax) |
| `Network` | [3](#calculate_tax) |
| `Println` | [12](#println) |
| `Processing` | [7](#unnamed_test) |
| `Pure` | [1](#features_1), [6](#double), [10](#pure_func), [14](#handle_request) |
| `PureFunc` | [10](#pure_func) |
| `Related` | [1](#features_1) |
| `Request` | [2](#calculate), [14](#handle_request) |
| `Response` | [2](#calculate), [14](#handle_request) |
| `Result` | [3](#calculate_tax), [12](#println) |
| `String` | [3](#calculate_tax), [12](#println) |
| `Tax` | [3](#calculate_tax) |
| `Unnamed` | [7](#unnamed_test), [8](#unnamed_test) |
| `Usage` | [8](#unnamed_test) |
| `Uses` | [7](#unnamed_test) |
| `Warning` | [4](#auto_inferred) |
| `add` | [5](#add) |
| `assert_compiles` | [1](#features_1), [11](#features_11) |
| `auto` | [4](#auto_inferred) |
| `auto_inferred` | [4](#auto_inferred) |
| `calculate` | [2](#calculate), [3](#calculate_tax), [9](#calculate), [13](#calculate_discount) |
| `calculate_discount` | [13](#calculate_discount), [14](#handle_request) |
| `calculate_tax` | [3](#calculate_tax) |
| `discount` | [13](#calculate_discount) |
| `double` | [6](#double), [8](#unnamed_test) |
| `download_and_save` | [3](#calculate_tax) |
| `download_and_save_correct` | [3](#calculate_tax) |
| `features` | [1](#features_1), [11](#features_11) |
| `fetch_data` | [3](#calculate_tax) |
| `fetch_multiplier` | [7](#unnamed_test) |
| `format_response` | [14](#handle_request) |
| `func` | [10](#pure_func) |
| `get` | [3](#calculate_tax), [12](#println) |
| `handle` | [14](#handle_request) |
| `handle_request` | [2](#calculate), [14](#handle_request) |
| `impure_func` | [10](#pure_func) |
| `impure_mistake` | [5](#add) |
| `impure_processor` | [7](#unnamed_test) |
| `inferred` | [4](#auto_inferred) |
| `log_and_double` | [6](#double) |
| `map` | [8](#unnamed_test) |
| `mistake` | [6](#double), [7](#unnamed_test) |
| `module` | [2](#calculate) |
| `multiply` | [6](#double) |
| `post` | [12](#println) |
| `print` | [12](#println) |
| `print_and_double` | [8](#unnamed_test) |
| `print_message` | [3](#calculate_tax) |
| `println` | [3](#calculate_tax), [4](#auto_inferred), [5](#add), [6](#double), [7](#unnamed_test), ... (9 total) |
| `process` | [2](#calculate) |
| `process_with_logging` | [7](#unnamed_test) |
| `processor` | [7](#unnamed_test) |
| `properly_annotated` | [4](#auto_inferred) |
| `pure` | [10](#pure_func) |
| `pure_func` | [10](#pure_func) |
| `pure_processor` | [7](#unnamed_test) |
| `push` | [8](#unnamed_test) |
| `randint` | [12](#println) |
| `randint_seeded` | [12](#println) |
| `read_file` | [12](#println) |
| `read_line` | [12](#println) |
| `request` | [14](#handle_request) |
| `return` | [13](#calculate_discount) |
| `sin` | [12](#println) |
| `sqrt` | [12](#println) |
| `tax` | [3](#calculate_tax) |
| `unnamed` | [7](#unnamed_test), [8](#unnamed_test) |
| `use_impure` | [8](#unnamed_test) |
| `use_it` | [7](#unnamed_test) |
| `use_pure` | [8](#unnamed_test) |
| `validate_age` | [13](#calculate_discount) |
| `version` | [12](#println) |
| `write` | [3](#calculate_tax) |
| `write_file` | [12](#println) |

---

## Test Cases (14 total)

| # | Test | Section | Symbols |
|---|------|---------|---------|
| 1 | [features_1](#features_1) | Features | `features`, `Features`, `Effect` +9 |
| 2 | [calculate](#calculate) | Features | `calculate`, `Calculate`, `Response` +5 |
| 3 | [calculate_tax](#calculate_tax) | Features | `Tax`, `calculate_tax`, `CalculateTax` +15 |
| 4 | [auto_inferred](#auto_inferred) | Features | `AutoInferred`, `auto_inferred`, `auto` +9 |
| 5 | [add](#add) | Features | `add`, `Add`, `impure_mistake` +2 |
| 6 | [double](#double) | Features | `double`, `Double`, `mistake` +6 |
| 7 | [unnamed_test](#unnamed_test) | Features | `unnamed`, `Unnamed`, `mistake` +13 |
| 8 | [unnamed_test](#unnamed_test) | Features | `unnamed`, `Unnamed`, `Effect` +9 |
| 9 | [calculate](#calculate) | Features | `calculate`, `Calculate`, `Error` +3 |
| 10 | [pure_func](#pure_func) | Features | `func`, `pure_func`, `pure` +7 |
| 11 | [features_11](#features_11) | Features | `features`, `Features`, `Error` +3 |
| 12 | [println](#println) | Features | `Println`, `println`, `read_line` +13 |
| 13 | [calculate_discount](#calculate_discount) | Examples | `CalculateDiscount`, `Calculate`, `calculate` +8 |
| 14 | [handle_request](#handle_request) | Examples | `Handle`, `HandleRequest`, `handle_request` +7 |

---

### Test 1: Features {#features_1}

**Test name:** `features_1`

**Linked Symbols:**
- `features`
- `Features`
- `Effect`
- `Compiler`
- `Capability`
- `assert_compiles`
- `ERROR`
- `Can`
- `Related`
- `Module`
- ... and 2 more

**Code:**

```simple
test "features_1":
    """
    Module-level capability requirements with compile-time checking.
    
    **Links:** Capability::requires, Effect::Module, Compiler::check
    **Related:** features_11
    """
    # Pure module - no side effects allowed
    module app.domain requires[pure]:
        use core.math.*        # OK - pure module
        use std.collections.*  # OK - pure module
        use io.fs.*            # ERROR: fs capability not declared

    # Module with specific capabilities
    module app.storage requires[io, fs]:
        use io.fs.*            # OK - fs declared
        use std.io.*           # OK - io declared
        use http.client.*      # ERROR: net capability not declared

    # Module with all capabilities
    module app.main requires[io, net, fs, unsafe]:
        # Can use anything
        use http.client.*      # OK
        use io.fs.*            # OK
    assert_compiles()
```

### Test 2: Features {#calculate}

**Test name:** `calculate`

**Description:**

### Scenario: Capability Inheritance:...

Capability Inheritance:

**Linked Symbols:**
- `calculate`
- `Calculate`
- `Response`
- `handle_request`
- `Module`
- `Request`
- `process`
- `module`

**Code:**

```simple
fn calculate(x: i64) -> i64:
        return x * 2

# Module using pure module (no capabilities needed)
module app.business requires[pure]:
    use app.core.*
    fn process(x: i64) -> i64:
        return calculate(x) + 1  # OK - core.calculate is pure

# Module adding I/O
module app.api requires[io, net]:
    use app.business.*
    use http.client.*
    
    fn handle_request(req: Request) -> Response:
        let result = process(req.value)  # OK
        return Response::ok(result)
```

### Test 3: Features {#calculate_tax}

**Test name:** `calculate_tax`

**Linked Symbols:**
- `Tax`
- `calculate_tax`
- `CalculateTax`
- `Calculate`
- `calculate`
- `tax`
- `fetch_data`
- `Multiple`
- `Network`
- `String`
- ... and 8 more

**Code:**

```simple
fn calculate_tax(amount: i64) -> i64:
    return amount * 15 / 100

# I/O function
@io
fn print_message(msg: String):
    println(msg)  # OK - @io allows stdout

# Network function
@net
fn fetch_data(url: String) -> Result<String>:
    return http.get(url)  # OK - @net allows network

# Multiple effects
@io @net
fn download_and_save(url: String, path: String):
    let data = http.get(url)?      # OK - @net
    fs.write(path, data)?          # ERROR - needs @fs

@io @net @fs
fn download_and_save_correct(url: String, path: String):
    let data = http.get(url)?      # OK
    fs.write(path, data)?          # OK
```

### Test 4: Features {#auto_inferred}

**Test name:** `auto_inferred`

**Description:**

### Scenario: Effect Inference:...

Effect Inference:

**Linked Symbols:**
- `AutoInferred`
- `auto_inferred`
- `auto`
- `Auto`
- `Inferred`
- `inferred`
- `Compiler`
- `println`
- `Warning`
- `Function`
- ... and 2 more

**Code:**

```simple
fn auto_inferred():
    # Compiler infers @io from println
    println("hello")
    # Warning: Function has effect @io but no annotation

# Add annotation to satisfy compiler
@io
fn properly_annotated():
    println("hello")  # OK
```

### Test 5: Features {#add}

**Test name:** `add`

**Description:**

### Scenario: Pure by Default:...

Pure by Default:

**Linked Symbols:**
- `add`
- `Add`
- `impure_mistake`
- `ERROR`
- `println`

**Code:**

```simple
fn add(x: i64, y: i64) -> i64:
    return x + y  # OK - pure operations only

fn impure_mistake():
    println("oops")  # ERROR: println requires @io
```

### Test 6: Features {#double}

**Test name:** `double`

**Linked Symbols:**
- `double`
- `Double`
- `mistake`
- `Impure`
- `println`
- `ERROR`
- `log_and_double`
- `multiply`
- `Pure`

**Code:**

```simple
fn double(x: i64) -> i64:
    return multiply(x, 2)  # OK if multiply is pure

# Pure function calling impure function - ERROR
@pure
fn mistake(x: i64):
    println(x)  # ERROR: @pure cannot call @io function

# Impure function calling anything - OK
@io
fn log_and_double(x: i64) -> i64:
    println("doubling {}", x)  # OK - @io allows this
    return double(x)            # OK - can call pure functions
```

### Test 7: Features {#unnamed_test}

**Test name:** `unnamed_test`

**Description:**

### Scenario: Capability Requirements:...

Capability Requirements:

**Linked Symbols:**
- `unnamed`
- `Unnamed`
- `mistake`
- `Done`
- `println`
- `impure_processor`
- `Processing`
- `use_it`
- `Cannot`
- `process_with_logging`
- ... and 6 more

**Code:**

```simple
fn process_with_logging<T>(value: T, processor: fn(T) -> T) -> T:
    println("Processing...")
    let result = processor(value)
    println("Done")
    return result

# Can pass pure functions
fn pure_processor(x: i64) -> i64:
    return x * 2

@io
fn use_it():
    let result = process_with_logging(5, pure_processor)  # OK

# Cannot pass impure functions without matching effects
@net
fn impure_processor(x: i64) -> i64:
    fetch_multiplier()  # Uses network
    return x * 2

@io
fn mistake():
    process_with_logging(5, impure_processor)  # ERROR: @net not available
```

### Test 8: Features {#unnamed_test}

**Test name:** `unnamed_test`

**Description:**

### Scenario: Generic Effect Constraints:...

Generic Effect Constraints:

**Linked Symbols:**
- `unnamed`
- `Unnamed`
- `Effect`
- `println`
- `print_and_double`
- `push`
- `use_impure`
- `map`
- `Usage`
- `double`
- ... and 2 more

**Code:**

```simple
fn map<T, U, E: Effect>(arr: [T], f: fn(T) -> U with E) -> [U] with E:
    let mut result = []
    for item in arr:
        result.push(f(item))
    return result

# Usage with pure function
@pure
fn double(x: i64) -> i64:
    return x * 2

fn use_pure():
    let nums = [1, 2, 3]
    let doubled = map(nums, double)  # Inferred as pure

# Usage with impure function
@io
fn print_and_double(x: i64) -> i64:
    println(x)
    return x * 2

@io
fn use_impure():
    let nums = [1, 2, 3]
    let doubled = map(nums, print_and_double)  # Inferred as @io
```

### Test 9: Features {#calculate}

**Test name:** `calculate`

**Linked Symbols:**
- `calculate`
- `Calculate`
- `Error`
- `println`
- `E0420`
- `ERROR`

**Code:**

```simple
fn calculate(x: i64) -> i64:
        println("calculating {}", x)  # ERROR
        return x * 2

# Error output:
error[E0420]: forbidden effect in pure context
  --> app.core:3:9
   |
 3 |         println("calculating {}", x)
   |         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ call to @io function
   |
   = note: function `calculate` is in pure module `app.core`
   = note: `println` requires @io capability
   = help: add @io to function or module requires[io]
```

### Test 10: Features {#pure_func}

**Test name:** `pure_func`

**Description:**

### Scenario: Effect Mismatch Errors:...

Effect Mismatch Errors:

**Linked Symbols:**
- `func`
- `pure_func`
- `pure`
- `Func`
- `PureFunc`
- `Pure`
- `Error`
- `E0421`
- `impure_func`
- `ERROR`

**Code:**

```simple
fn pure_func():
    impure_func()  # ERROR

@io @net
fn impure_func():
    ...

# Error output:
error[E0421]: effect mismatch
  --> example.spl:3:5
   |
 3 |     impure_func()
   |     ^^^^^^^^^^^^^ calls function requiring @io @net
   |
   = note: function `pure_func` is marked @pure
   = note: `impure_func` requires effects: @io, @net
   = help: add required effects to `pure_func`:
           @io @net
           fn pure_func():
```

### Test 11: Features {#features_11}

**Test name:** `features_11`

**Description:**

### Scenario: Capability Not Available:...

Capability Not Available:

**Linked Symbols:**
- `features`
- `Features`
- `Error`
- `assert_compiles`
- `ERROR`
- `E0422`

**Code:**

```simple
test "features_11":
    """
    Features
    """
    module app.domain requires[pure]:
        use io.fs.*  # ERROR

    # Error output:
    error[E0422]: capability not available
      --> app.domain:2:9
       |
     2 |     use io.fs.*
       |         ^^^^^^^ module requires @fs capability
       |
       = note: module `app.domain` declares requires[pure]
       = note: module `io.fs` requires capability: @fs
       = help: add @fs to module declaration:
               module app.domain requires[fs]:
    assert_compiles()
```

### Test 12: Features {#println}

**Test name:** `println`

**Linked Symbols:**
- `Println`
- `println`
- `read_line`
- `Result`
- `randint_seeded`
- `String`
- `write_file`
- `Deterministic`
- `post`
- `read_file`
- ... and 6 more

**Code:**

```simple
fn println(msg: String):
        ...
    
    @io
    fn print(msg: String):
        ...
    
    @io
    fn read_line() -> String:
        ...

# std/fs.spl
module std.fs:
    @fs
    fn read_file(path: String) -> Result<String>:
        ...
    
    @fs
    fn write_file(path: String, content: String) -> Result<()>:
        ...

# std/http.spl
module std.http:
    @net
    fn get(url: String) -> Result<String>:
        ...
    
    @net
    fn post(url: String, body: String) -> Result<String>:
        ...

# std/math.spl
module std.math requires[pure]:
    @pure
    fn sqrt(x: f64) -> f64:
        ...
    
    @pure
    fn sin(x: f64) -> f64:
        ...

# std/random.spl
module std.random:
    @random
    fn randint(min: i64, max: i64) -> i64:
        ...
    
    # Deterministic version (pure with seed)
    @pure
    fn randint_seeded(min: i64, max: i64, seed: u64) -> i64:
        ...
```

### Test 13: Examples {#calculate_discount}

**Test name:** `calculate_discount`

**Description:**

### Scenario: ### LLM-Safe Pure Module...

### LLM-Safe Pure Module

**Linked Symbols:**
- `CalculateDiscount`
- `Calculate`
- `calculate`
- `discount`
- `Discount`
- `calculate_discount`
- `println`
- `validate_age`
- `ERROR`
- `return`
- ... and 1 more

**Code:**

```simple
fn calculate_discount(price: i64, rate: f64) -> i64:
        return (price as f64 * (1.0 - rate)) as i64
    
    fn validate_age(age: i64) -> bool:
        return age >= 18 and age < 120
    
    # LLM cannot add logging here
    # println("calculating")  # ERROR: @io not available
```

### Test 14: Examples {#handle_request}

**Test name:** `handle_request`

**Description:**

### Scenario: ### Explicit I/O Boundaries...

### Explicit I/O Boundaries

**Linked Symbols:**
- `Handle`
- `HandleRequest`
- `handle_request`
- `handle`
- `request`
- `Request`
- `format_response`
- `Response`
- `Pure`
- `calculate_discount`

**Code:**

```simple
fn handle_request(req: Request) -> Response:
        # I/O boundary is explicit
        let discount = calculate_discount(req.price, 0.1)  # Pure
        let response_body = format_response(discount)     # Pure
        return Response::ok(response_body)                # I/O
```

---

## Source Code

**View full specification:** [capability_effects_spec.spl](../../tests/specs/capability_effects_spec.spl)

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/capability_effects_spec.spl`*
