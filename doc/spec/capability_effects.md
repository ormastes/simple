# Capability-Based Effects Specification (#880-884)

> **⚠️ MIGRATED:** This specification has been migrated to an executable test file:  
> **→** `tests/specs/capability_effects_spec.spl`  
> **Date:** 2026-01-09  
> 
> This file is kept for reference but may become outdated. The _spec.spl file is the source of truth.

**Status:** 📋 Planned  
**Category:** LLM-Friendly Features  
**Priority:** High  
**Difficulty:** 2-4

## Overview

Capability-based effect system that prevents LLMs from silently adding I/O or stateful behavior to pure code. Explicit effect markers (`@pure`, `@io`, `@net`, `@fs`) make side effects visible and checked at compile time.

## Motivation

**Problem:**
- LLMs often add I/O calls without realizing constraints
- Pure functions become impure silently
- Side effects spread through codebase uncontrolled
- Testing becomes difficult (hidden I/O)

**Solution:**
- Explicit effect annotations required
- Module-level capability declarations
- Compile-time capability checking
- Clear errors when violations occur

## Features

### #880: `module requires[cap]` (Difficulty: 3)

**Module-Level Capability Declaration:**

```simple
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
```

**Capability Types:**
- `pure` - No side effects (default assumption if not specified)
- `io` - General I/O operations (stdin/stdout/stderr)
- `fs` - Filesystem access
- `net` - Network operations
- `unsafe` - Unsafe operations (FFI, raw pointers)
- `random` - Non-deterministic random numbers
- `time` - Current time/date access
- `env` - Environment variables

**Capability Inheritance:**
```simple
# Pure module
module app.core requires[pure]:
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

### #881: `@pure` / `@io` / `@net` Effect Annotations (Difficulty: 2)

**Function-Level Effect Annotations:**

```simple
# Pure function - no side effects
@pure
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

**Effect Inference:**
```simple
# Automatically infer effects from body
fn auto_inferred():
    # Compiler infers @io from println
    println("hello")
    # Warning: Function has effect @io but no annotation

# Add annotation to satisfy compiler
@io
fn properly_annotated():
    println("hello")  # OK
```

**Pure by Default:**
```simple
# Functions without annotations assumed pure
fn add(x: i64, y: i64) -> i64:
    return x + y  # OK - pure operations only

fn impure_mistake():
    println("oops")  # ERROR: println requires @io
```

### #882: Capability Propagation (Difficulty: 4)

**Effect Propagation Rules:**

```simple
# Pure function calling pure function - OK
@pure
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

**Capability Requirements:**
```simple
# Function requiring specific capabilities
@io
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

**Generic Effect Constraints:**
```simple
# Generic function with effect constraint
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

### #883: Forbidden Effect Errors (Difficulty: 2)

**Clear Error Messages:**

```simple
# Example error
module app.core requires[pure]:
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

**Effect Mismatch Errors:**
```simple
@pure
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

**Capability Not Available:**
```simple
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
```

### #884: Stdlib Effect Annotations (Difficulty: 2)

**Annotate All Stdlib Functions:**

```simple
# std/io.spl
module std.io:
    @io
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

## Implementation

### Capability Checking Algorithm

**Phase 1: Parse Annotations**
```rust
struct FunctionDef {
    name: String,
    effects: HashSet<Effect>,
    body: Vec<Statement>,
}

enum Effect {
    Pure,
    Io,
    Net,
    Fs,
    Unsafe,
    Random,
    Time,
    Env,
}
```

**Phase 2: Infer Effects**
```rust
fn infer_effects(func: &FunctionDef) -> HashSet<Effect> {
    let mut effects = HashSet::new();
    
    for stmt in &func.body {
        // Check function calls
        if let Statement::Call(call) = stmt {
            let callee_effects = get_function_effects(&call.function);
            effects.extend(callee_effects);
        }
    }
    
    effects
}
```

**Phase 3: Check Compatibility**
```rust
fn check_effect_compatibility(
    declared: &HashSet<Effect>,
    inferred: &HashSet<Effect>,
    module_caps: &HashSet<Effect>
) -> Result<(), EffectError> {
    // Check declared effects match inferred
    if !inferred.is_subset(declared) {
        let missing = inferred.difference(declared);
        return Err(EffectError::MissingDeclaration(missing));
    }
    
    // Check module capabilities allow effects
    if !declared.is_subset(module_caps) {
        let forbidden = declared.difference(module_caps);
        return Err(EffectError::ForbiddenInModule(forbidden));
    }
    
    Ok(())
}
```

### Effect Propagation

```rust
fn propagate_effects(module: &Module) -> Result<(), EffectError> {
    let mut effect_map = HashMap::new();
    
    // Build effect map
    for func in &module.functions {
        let inferred = infer_effects(func);
        effect_map.insert(&func.name, inferred);
    }
    
    // Check all call sites
    for func in &module.functions {
        check_calls(func, &effect_map, &module.capabilities)?;
    }
    
    Ok(())
}
```

## Benefits for LLM Tools

1. **Prevents Silent I/O** - LLMs cannot add I/O without declaration
2. **Clear Constraints** - Effect requirements explicit
3. **Early Detection** - Compile-time checking
4. **Self-Documenting** - Effects visible in signatures
5. **Testing** - Pure functions easy to test

## Implementation Plan

### Phase 1: Parser Support (2 days)
- [ ] Parse `@pure`, `@io`, `@net`, `@fs` annotations
- [ ] Parse `module requires[cap]` syntax
- [ ] AST nodes for effects
- [ ] Tests for parsing

### Phase 2: Effect Inference (2 days)
- [ ] Infer effects from function bodies
- [ ] Track effects through call graph
- [ ] Handle generic functions
- [ ] Tests for inference

### Phase 3: Capability Checking (2 days)
- [ ] Check module capabilities
- [ ] Check function effects
- [ ] Propagation algorithm
- [ ] Tests for checking

### Phase 4: Error Messages (1 day)
- [ ] Clear error messages
- [ ] Helpful suggestions
- [ ] Error codes (E0420-E0422)
- [ ] Tests for errors

### Phase 5: Stdlib Annotations (2 days)
- [ ] Annotate all stdlib functions
- [ ] Document effect requirements
- [ ] Test stdlib annotations
- [ ] Examples and guide

**Total Estimated Effort:** 9 days

## File Structure

```
src/compiler/src/effects/
├── mod.rs               # Main effects module
├── checker.rs           # Effect checking
├── inference.rs         # Effect inference
├── propagation.rs       # Effect propagation
└── errors.rs            # Effect errors

simple/std_lib/src/
├── io.spl              # @io annotations
├── fs.spl              # @fs annotations
├── http.spl            # @net annotations
├── random.spl          # @random annotations
└── math.spl            # @pure annotations

simple/std_lib/test/system/effects/
├── pure_spec.spl       # Pure function tests
├── io_spec.spl         # I/O effect tests
├── net_spec.spl        # Network effect tests
└── propagation_spec.spl # Effect propagation tests
```

## Examples

### LLM-Safe Pure Module
```simple
module app.business requires[pure]:
    use std.math.*
    use std.collections.*
    
    fn calculate_discount(price: i64, rate: f64) -> i64:
        return (price as f64 * (1.0 - rate)) as i64
    
    fn validate_age(age: i64) -> bool:
        return age >= 18 and age < 120
    
    # LLM cannot add logging here
    # println("calculating")  # ERROR: @io not available
```

### Explicit I/O Boundaries
```simple
module app.api requires[io, net]:
    use app.business.*  # Pure module
    use http.client.*
    
    @io @net
    fn handle_request(req: Request) -> Response:
        # I/O boundary is explicit
        let discount = calculate_discount(req.price, 0.1)  # Pure
        let response_body = format_response(discount)     # Pure
        return Response::ok(response_body)                # I/O
```

## Related Features

- #889: Semantic diff (detects effect changes)
- #916-919: Sandboxed execution (enforces capabilities)
- #911: Deterministic builds (pure code is deterministic)

## Success Metrics

- [ ] 100% of stdlib annotated
- [ ] Zero false positives
- [ ] LLM-generated code respects effects
- [ ] <5% effect violations in LLM output
- [ ] 90%+ developer satisfaction

## References

- **Koka** (Microsoft) - Effect system with handlers
- **Eff** (Language) - Algebraic effects
- **OCaml** - Pure vs impure separation
- **Haskell IO Monad** - Effect isolation

---

**Next Steps:**
1. Review and approve specification
2. Implement parser support
3. Add effect checking
4. Annotate stdlib
5. Mark #880-884 complete
