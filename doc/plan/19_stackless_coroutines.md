# Stackless Coroutine Implementation Plan (Yield/Generator Codegen)

## Overview

This plan describes how to implement true stackless coroutines for the `Yield` instruction (trap 37) and complete the `GeneratorCreate`/`GeneratorNext` instructions in compiled code.

## Current State

### Interpreter Implementation (Eager)

The interpreter has a simplified "eager" generator that:
- Executes the entire generator body upfront
- Collects all yielded values into a list
- `next()` returns values from the pre-computed list

This works but:
- Cannot support infinite generators
- No true suspension/resumption
- Wastes memory for large generators

### MIR Instructions

```rust
GeneratorCreate { dest: VReg, body_block: BlockId }  // Creates generator
Yield { value: VReg }                                // Yields value, suspends
GeneratorNext { dest: VReg, generator: VReg }        // Resumes, gets next value
```

### Current Codegen Status

- `GeneratorCreate`: Calls `rt_generator_new(body_func)` - creates stub wrapper
- `GeneratorNext`: Calls `rt_generator_next(gen)` - returns last yielded value
- `Yield`: **Trap 37** - not implemented

---

## The Challenge: Yield

`Yield` is fundamentally different from other instructions because it:
1. **Suspends execution** - must save current state
2. **Resumes later** - must restore state and continue
3. **Crosses call boundaries** - caller's stack frame is gone when resumed

This requires **state machine transformation** - converting the generator body into a state machine where each yield point becomes a state.

---

## Implementation Approaches

### Approach 1: CPS Transformation (Continuation-Passing Style)

Transform generator body to continuation-passing style at MIR level.

**Before:**
```
block0:
    v0 = const 1
    yield v0
    v1 = const 2
    yield v1
    return
```

**After:**
```
generator_state = { state: 0, locals: {} }

block0_state0:
    v0 = const 1
    generator_state.yielded = v0
    generator_state.state = 1
    return

block0_state1:
    v1 = const 2
    generator_state.yielded = v1
    generator_state.state = 2
    return

block0_state2:
    generator_state.state = COMPLETED
    return
```

**Pros:**
- Clean transformation at MIR level
- Works well with existing codegen
- No special runtime support needed

**Cons:**
- Complex MIR transformation
- Code size explosion for many yield points
- Need to save/restore all live variables

### Approach 2: Stackful Coroutines (Fiber/Green Thread)

Use OS-level or custom stack switching.

**Pros:**
- No code transformation needed
- Supports arbitrary yield patterns
- Simple mental model

**Cons:**
- Platform-specific (needs assembly)
- Stack allocation overhead
- Not compatible with Cranelift's model

### Approach 3: Async/Await State Machine (Rust-style)

Transform to state machine similar to Rust's async/await.

**Generator becomes:**
```rust
enum GeneratorState {
    Start,
    Yield0 { /* saved locals */ },
    Yield1 { /* saved locals */ },
    Complete,
}

fn poll(state: &mut GeneratorState) -> Option<Value> {
    match state {
        Start => {
            let v0 = 1;
            *state = Yield0 { /* save */ };
            Some(v0)
        }
        Yield0 { .. } => {
            let v1 = 2;
            *state = Yield1 { /* save */ };
            Some(v1)
        }
        Yield1 { .. } => {
            *state = Complete;
            None
        }
        Complete => None,
    }
}
```

**Pros:**
- Well-understood pattern (Rust uses this)
- Efficient (no stack allocation)
- Works with Cranelift

**Cons:**
- Requires MIR transformation pass
- Must track live variables at each yield

---

## Recommended Approach: Approach 3 (Async State Machine)

### Why?

1. **Proven pattern** - Rust's async/await uses this successfully
2. **No platform assembly** - Pure MIR transformation
3. **Efficient** - State stored in heap, no stack switching
4. **Composable** - Generators can nest

---

## Implementation Plan

### Phase 1: MIR Yield Analysis

Add a MIR analysis pass to identify:
- All yield points in a function
- Live variables at each yield point
- Control flow between yields

```rust
struct YieldPoint {
    block: BlockId,
    inst_index: usize,
    live_vars: Vec<VReg>,
    resume_block: BlockId,
}

fn analyze_yields(func: &MirFunction) -> Vec<YieldPoint> {
    // Walk function, find all Yield instructions
    // Compute live variables at each yield
}
```

### Phase 2: State Machine Transformation

Transform generator functions into state machines:

```rust
fn transform_generator(func: MirFunction) -> MirFunction {
    let yields = analyze_yields(&func);

    // 1. Create state enum type
    // 2. Replace function body with state machine
    // 3. Each yield becomes a state transition
    // 4. Save live variables to state struct
    // 5. Restore on resume
}
```

**Generated state struct:**
```rust
struct GeneratorState_N {
    state: u32,           // Current state index
    yielded: RuntimeValue, // Last yielded value
    // Saved locals for each yield point
    yield0_v1: RuntimeValue,
    yield0_v2: RuntimeValue,
    yield1_v1: RuntimeValue,
    // ...
}
```

### Phase 3: Runtime Support

Update `RuntimeGenerator` in `value.rs`:

```rust
#[repr(C)]
pub struct RuntimeGenerator {
    pub header: HeapHeader,
    pub state: u64,           // Current state index
    pub yielded: RuntimeValue, // Last yielded value
    pub body_func: u64,       // Pointer to state machine function
    pub state_data: *mut u8,  // Pointer to saved locals
    pub state_size: u64,      // Size of state data
}

/// Create generator with state machine function
#[no_mangle]
pub extern "C" fn rt_generator_new(body_func: u64, state_size: u64) -> RuntimeValue {
    // Allocate RuntimeGenerator
    // Allocate state_data of state_size bytes
    // Initialize state = 0 (Start)
}

/// Resume generator, get next value
#[no_mangle]
pub extern "C" fn rt_generator_next(gen: RuntimeValue) -> RuntimeValue {
    // Get generator state
    // Call body_func(state_data) - advances state machine
    // Return yielded value, or NIL if complete
}

/// Called by generated code to yield a value
#[no_mangle]
pub extern "C" fn rt_generator_yield(gen: RuntimeValue, value: RuntimeValue, next_state: u64) {
    // Save yielded value
    // Update state index
}
```

### Phase 4: Codegen Updates

**GeneratorCreate:**
```rust
MirInst::GeneratorCreate { dest, body_block } => {
    // Get transformed state machine function pointer
    let body_func = self.get_generator_func_ptr(body_block);
    let state_size = self.get_generator_state_size(body_block);

    let new_id = self.runtime_funcs["rt_generator_new"];
    let new_ref = self.module.declare_func_in_func(new_id, builder.func);

    let func_ptr = builder.ins().iconst(types::I64, body_func as i64);
    let size_val = builder.ins().iconst(types::I64, state_size as i64);
    let call = builder.ins().call(new_ref, &[func_ptr, size_val]);
    vreg_values.insert(*dest, builder.inst_results(call)[0]);
}
```

**Yield (in transformed code):**
```rust
// Yield becomes:
// 1. Store yielded value
// 2. Store next state
// 3. Return

let yield_id = self.runtime_funcs["rt_generator_yield"];
let yield_ref = self.module.declare_func_in_func(yield_id, builder.func);
let gen_ptr = /* generator pointer from closure/context */;
let value = vreg_values[&yield_value];
let next_state = builder.ins().iconst(types::I64, state_index as i64);
builder.ins().call(yield_ref, &[gen_ptr, value, next_state]);
builder.ins().return_(&[]);
```

**GeneratorNext:**
```rust
MirInst::GeneratorNext { dest, generator } => {
    let next_id = self.runtime_funcs["rt_generator_next"];
    let next_ref = self.module.declare_func_in_func(next_id, builder.func);
    let gen_val = vreg_values[generator];
    let call = builder.ins().call(next_ref, &[gen_val]);
    vreg_values.insert(*dest, builder.inst_results(call)[0]);
}
```

---

## Example Transformation

### Source
```simple
def count_to(n):
    let i = 0
    while i < n:
        yield i
        i = i + 1
```

### MIR Before
```
count_to(n):
  block0:
    v0 = const 0         ; i = 0
    jump block1
  block1:
    v1 = lt v0, n        ; i < n
    brif v1 block2 block3
  block2:
    yield v0             ; yield i
    v2 = add v0, 1       ; i = i + 1
    v0 = copy v2
    jump block1
  block3:
    return nil
```

### MIR After (State Machine)
```
count_to_generator(state_ptr):
  ; Load state
  v_state = load state_ptr, 0
  v_i = load state_ptr, 8
  v_n = load state_ptr, 16

  switch v_state:
    0 -> state0
    1 -> state1
    _ -> complete

  state0:  ; Initial state
    v_i = const 0
    store state_ptr, 8, v_i     ; Save i
    ; Fall through to check

  check:
    v_cond = lt v_i, v_n
    brif v_cond yield_state complete

  yield_state:
    ; Yield i
    store state_ptr, 24, v_i    ; yielded = i
    v_next_i = add v_i, 1
    store state_ptr, 8, v_next_i ; Save i for next resume
    store state_ptr, 0, 1       ; state = 1 (resume after yield)
    return

  state1:  ; Resume after yield
    jump check

  complete:
    store state_ptr, 0, 2       ; state = complete
    store state_ptr, 24, nil    ; yielded = nil
    return
```

---

## Testing Strategy

### Unit Tests

```rust
#[test]
fn test_generator_simple() {
    let gen = rt_generator_new(simple_gen as u64, 32);
    assert_eq!(rt_generator_next(gen).as_int(), 1);
    assert_eq!(rt_generator_next(gen).as_int(), 2);
    assert!(rt_generator_next(gen).is_nil());
}

#[test]
fn test_generator_with_state() {
    // Generator that yields 0..n
    let gen = create_count_generator(5);
    for i in 0..5 {
        assert_eq!(rt_generator_next(gen).as_int(), i);
    }
    assert!(rt_generator_next(gen).is_nil());
}
```

### Integration Tests

```rust
#[test]
fn test_compiled_generator() {
    let src = r#"
        gen = generator(\:
            yield 1
            yield 2
            yield 3
        )
        a = next(gen)
        b = next(gen)
        c = next(gen)
        return a + b + c  # Should be 6
    "#;
    assert_eq!(runner.run_source(src), 6);
}

#[test]
fn test_generator_with_loop() {
    let src = r#"
        def range(n):
            i = 0
            while i < n:
                yield i
                i = i + 1

        gen = range(5)
        sum = 0
        while True:
            v = next(gen)
            if v == nil:
                break
            sum = sum + v
        return sum  # 0+1+2+3+4 = 10
    "#;
    assert_eq!(runner.run_source(src), 10);
}
```

---

## Implementation Order

1. **Analysis pass**: Yield point detection and live variable analysis
2. **State struct generation**: Create state layout for each generator
3. **MIR transformation**: Convert generators to state machines
4. **Runtime updates**: Update `RuntimeGenerator` and FFI functions
5. **Codegen updates**: Handle transformed generators
6. **Remove trap**: Replace trap 37 with actual implementation
7. **Testing**: Unit and integration tests

---

## Estimated Effort

| Task | Effort |
|------|--------|
| Yield analysis pass | 3-4 hours |
| State struct generation | 2-3 hours |
| MIR transformation | 6-8 hours |
| Runtime FFI updates | 2 hours |
| Codegen updates | 2-3 hours |
| Testing | 3-4 hours |
| **Total** | **18-24 hours** |

---

## Dependencies

- Live variable analysis (may need to add to MIR)
- Generator body block compilation (similar to closures)
- RuntimeGenerator struct (already exists, needs updates)

## Future Enhancements

- **Async generators**: Combine with FutureCreate/Await
- **Generator delegation**: `yield from other_gen`
- **Bidirectional generators**: `send(gen, value)` to send values in
- **Infinite generators**: Already supported by state machine approach
- **Iterator protocol**: Make generators implement standard iteration
