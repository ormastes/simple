# Capability-Based Effects Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/capability_effects_spec.spl`
> **Generated:** 2026-01-09 04:37:07
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/capability_effects_spec.spl
> ```

**Status:** 📋 Planned
**Feature IDs:** **Keywords:**

## Overview

Capability-based effect system that prevents LLMs from silently adding I/O or stateful behavior to pure code. Explicit effect markers (`@pure`, `@io`, `@net`, `@fs`) make side effects visible and checked at compile time.

---

## Test Cases (14 total)

| Test | Section | Description |
|------|---------|-------------|
| [features_1](#test-1) | Features |  |
| [calculate](#test-2) | Features | ### Scenario: Capability Inheritance:...... |
| [calculate_tax](#test-3) | Features |  |
| [auto_inferred](#test-4) | Features | ### Scenario: Effect Inference:...  Effect Inference: |
| [add](#test-5) | Features | ### Scenario: Pure by Default:...  Pure by Default: |
| [double](#test-6) | Features |  |
| [unnamed_test](#test-7) | Features | ### Scenario: Capability Requirements:...... |
| [unnamed_test](#test-8) | Features | ### Scenario: Generic Effect Constraints:...... |
| [calculate](#test-9) | Features |  |
| [pure_func](#test-10) | Features | ### Scenario: Effect Mismatch Errors:...... |
| [features_11](#test-11) | Features | ### Scenario: Capability Not Available:...... |
| [println](#test-12) | Features |  |
| [calculate_discount](#test-13) | Examples | ### Scenario: ### LLM-Safe Pure Module...... |
| [handle_request](#test-14) | Examples | ### Scenario: ### Explicit I/O Boundaries...... |

---

### Test 1: Features

**Test name:** `features_1`

**Code:**

```simple
test "features_1":
    """
    Features
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

### Test 2: Features

**Test name:** `calculate`

**Description:**

### Scenario: Capability Inheritance:...

Capability Inheritance:

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

### Test 3: Features

**Test name:** `calculate_tax`

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

### Test 4: Features

**Test name:** `auto_inferred`

**Description:**

### Scenario: Effect Inference:...

Effect Inference:

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

### Test 5: Features

**Test name:** `add`

**Description:**

### Scenario: Pure by Default:...

Pure by Default:

**Code:**

```simple
fn add(x: i64, y: i64) -> i64:
    return x + y  # OK - pure operations only

fn impure_mistake():
    println("oops")  # ERROR: println requires @io
```

### Test 6: Features

**Test name:** `double`

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

### Test 7: Features

**Test name:** `unnamed_test`

**Description:**

### Scenario: Capability Requirements:...

Capability Requirements:

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

### Test 8: Features

**Test name:** `unnamed_test`

**Description:**

### Scenario: Generic Effect Constraints:...

Generic Effect Constraints:

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

### Test 9: Features

**Test name:** `calculate`

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

### Test 10: Features

**Test name:** `pure_func`

**Description:**

### Scenario: Effect Mismatch Errors:...

Effect Mismatch Errors:

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

### Test 11: Features

**Test name:** `features_11`

**Description:**

### Scenario: Capability Not Available:...

Capability Not Available:

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

### Test 12: Features

**Test name:** `println`

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

### Test 13: Examples

**Test name:** `calculate_discount`

**Description:**

### Scenario: ### LLM-Safe Pure Module...

### LLM-Safe Pure Module

**Code:**

```simple
fn calculate_discount(price: i64, rate: f64) -> i64:
        return (price as f64 * (1.0 - rate)) as i64
    
    fn validate_age(age: i64) -> bool:
        return age >= 18 and age < 120
    
    # LLM cannot add logging here
    # println("calculating")  # ERROR: @io not available
```

### Test 14: Examples

**Test name:** `handle_request`

**Description:**

### Scenario: ### Explicit I/O Boundaries...

### Explicit I/O Boundaries

**Code:**

```simple
fn handle_request(req: Request) -> Response:
        # I/O boundary is explicit
        let discount = calculate_discount(req.price, 0.1)  # Pure
        let response_body = format_response(discount)     # Pure
        return Response::ok(response_body)                # I/O
```

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/capability_effects_spec.spl`*
