# Codegen Architecture and FFI

Part of [Codegen Technical Documentation](codegen_technical.md).

## Architecture Diagrams

### Compilation Pipeline

```
Source Code (.spl)
       │
       ▼
   ┌─────────┐
   │  Lexer  │  → Tokens (with INDENT/DEDENT)
   └────┬────┘
        │
        ▼
   ┌─────────┐
   │ Parser  │  → AST
   └────┬────┘
        │
        ▼
   ┌─────────┐
   │   HIR   │  → Type-checked IR
   └────┬────┘
        │
        ▼
   ┌─────────┐
   │   MIR   │  → 50+ instructions with effects
   └────┬────┘
        │
    ┌───┴───────────────────────┐
    │                           │
    ▼                           ▼
┌──────────────┐        ┌───────────────┐
│  Outlining   │        │  Direct Code  │
│  Transform   │        │  Generation   │
│  (Feature 99)│        │               │
└──────┬───────┘        └───────┬───────┘
       │                        │
       ▼                        ▼
┌──────────────┐        ┌───────────────┐
│  Generator   │        │  Cranelift    │
│  Lowering    │        │  Backend      │
│  (#101)      │        │               │
└──────┬───────┘        └───────┬───────┘
       │                        │
       └────────────┬───────────┘
                    │
                    ▼
              ┌─────────┐
              │   SMF   │  → Binary module format
              └────┬────┘
                   │
                   ▼
              ┌─────────┐
              │ Loader  │  → Memory-mapped executable
              └────┬────┘
                   │
                   ▼
              Execution
```

### Runtime FFI Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                      Compiled Code (Cranelift)                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐ │
│  │ Value Creation  │  │   Collections   │  │  Async/Gen      │ │
│  │                 │  │                 │  │                 │ │
│  │ rt_value_int    │  │ rt_array_new    │  │ rt_actor_spawn  │ │
│  │ rt_value_float  │  │ rt_array_push   │  │ rt_future_new   │ │
│  │ rt_value_bool   │  │ rt_tuple_new    │  │ rt_generator_*  │ │
│  │ rt_value_nil    │  │ rt_dict_new     │  │                 │ │
│  └────────┬────────┘  └────────┬────────┘  └────────┬────────┘ │
│           │                    │                    │          │
└───────────┼────────────────────┼────────────────────┼──────────┘
            │                    │                    │
            ▼                    ▼                    ▼
┌─────────────────────────────────────────────────────────────────┐
│                     Runtime Library (Rust)                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────────────────────────────────────────────────────┐│
│  │  RuntimeValue (64-bit tagged pointer)                       ││
│  │  ┌──────────┬───────────────────────────────────────────┐   ││
│  │  │ Tag (3b) │              Payload (61 bits)            │   ││
│  │  └──────────┴───────────────────────────────────────────┘   ││
│  │                                                             ││
│  │  Tags: INT, FLOAT, BOOL, NIL, HEAP_PTR                      ││
│  └─────────────────────────────────────────────────────────────┘│
│                                                                 │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐ │
│  │ HeapHeader  │  │RuntimeArray │  │ RuntimeGenerator        │ │
│  │             │  │RuntimeTuple │  │ ┌───────────────────┐   │ │
│  │ object_type │  │RuntimeDict  │  │ │ state: u64        │   │ │
│  │ size        │  │RuntimeString│  │ │ slots: Vec<Value> │   │ │
│  │ gc_metadata │  │             │  │ │ ctx: RuntimeValue │   │ │
│  └─────────────┘  └─────────────┘  │ │ body_func: *fn    │   │ │
│                                    │ │ done: bool        │   │ │
│                                    │ └───────────────────┘   │ │
│                                    └─────────────────────────┘ │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## Runtime FFI Interface

Location: `src/compiler/src/codegen/runtime_ffi.rs`

### Function Specification Format

```rust
pub struct RuntimeFuncSpec {
    pub name: &'static str,      // Function name (e.g., "rt_array_new")
    pub params: &'static [Type], // Parameter types
    pub returns: &'static [Type],// Return types (empty for void)
}
```

### Complete FFI Function List

| Category | Function | Signature |
|----------|----------|-----------|
| **Array** | `rt_array_new` | `(i64) -> i64` |
| | `rt_array_push` | `(i64, i64) -> i8` |
| | `rt_array_get` | `(i64, i64) -> i64` |
| | `rt_array_set` | `(i64, i64, i64) -> i8` |
| | `rt_array_pop` | `(i64) -> i64` |
| | `rt_array_clear` | `(i64) -> i8` |
| **Tuple** | `rt_tuple_new` | `(i64) -> i64` |
| | `rt_tuple_set` | `(i64, i64, i64) -> i8` |
| | `rt_tuple_get` | `(i64, i64) -> i64` |
| | `rt_tuple_len` | `(i64) -> i64` |
| **Dict** | `rt_dict_new` | `(i64) -> i64` |
| | `rt_dict_set` | `(i64, i64, i64) -> i8` |
| | `rt_dict_get` | `(i64, i64) -> i64` |
| | `rt_dict_len` | `(i64) -> i64` |
| | `rt_dict_clear` | `(i64) -> i8` |
| | `rt_dict_keys` | `(i64) -> i64` |
| | `rt_dict_values` | `(i64) -> i64` |
| **Index/Slice** | `rt_index_get` | `(i64, i64) -> i64` |
| | `rt_index_set` | `(i64, i64, i64) -> i8` |
| | `rt_slice` | `(i64, i64, i64, i64) -> i64` |
| | `rt_contains` | `(i64, i64) -> i8` |
| **String** | `rt_string_new` | `(i64, i64) -> i64` |
| | `rt_string_concat` | `(i64, i64) -> i64` |
| **Value** | `rt_value_int` | `(i64) -> i64` |
| | `rt_value_float` | `(f64) -> i64` |
| | `rt_value_bool` | `(i8) -> i64` |
| | `rt_value_nil` | `() -> i64` |
| **Object** | `rt_object_new` | `(i32, i32) -> i64` |
| | `rt_object_field_get` | `(i64, i32) -> i64` |
| | `rt_object_field_set` | `(i64, i32, i64) -> i8` |
| **Closure** | `rt_closure_new` | `(i64, i32) -> i64` |
| | `rt_closure_set_capture` | `(i64, i32, i64) -> i8` |
| | `rt_closure_get_capture` | `(i64, i32) -> i64` |
| | `rt_closure_func_ptr` | `(i64) -> i64` |
| **Enum** | `rt_enum_new` | `(i32, i32, i64) -> i64` |
| | `rt_enum_discriminant` | `(i64) -> i64` |
| | `rt_enum_payload` | `(i64) -> i64` |
| **Memory** | `rt_alloc` | `(i64) -> i64` |
| | `rt_free` | `(i64, i64) -> ()` |
| | `rt_ptr_to_value` | `(i64) -> i64` |
| | `rt_value_to_ptr` | `(i64) -> i64` |
| **Async** | `rt_wait` | `(i64) -> i64` |
| | `rt_future_new` | `(i64, i64) -> i64` |
| | `rt_future_await` | `(i64) -> i64` |
| | `rt_actor_spawn` | `(i64, i64) -> i64` |
| | `rt_actor_send` | `(i64, i64) -> ()` |
| | `rt_actor_recv` | `() -> i64` |
| **Generator** | `rt_generator_new` | `(i64, i64, i64) -> i64` |
| | `rt_generator_next` | `(i64) -> i64` |
| | `rt_generator_get_state` | `(i64) -> i64` |
| | `rt_generator_set_state` | `(i64, i64) -> ()` |
| | `rt_generator_store_slot` | `(i64, i64, i64) -> ()` |
| | `rt_generator_load_slot` | `(i64, i64) -> i64` |
| | `rt_generator_get_ctx` | `(i64) -> i64` |
| | `rt_generator_mark_done` | `(i64) -> ()` |
| **Interpreter** | `rt_interp_call` | `(i64, i64, i64) -> i64` |
| | `rt_interp_eval` | `(i64) -> i64` |
| **Error** | `rt_function_not_found` | `(i64, i64) -> i64` |
| | `rt_method_not_found` | `(i64, i64, i64, i64) -> i64` |

---

## Testing Strategy

### Test Coverage by Feature

| Feature | Unit Tests | Integration Tests | System Tests |
|---------|-----------|-------------------|--------------|
| Body Block Outlining | `mir::generator::tests` | Interpreter tests | Runner tests |
| Generator State Machine | `splits_blocks_and_collects_states` | `generator_state_machine_runs_dispatcher` | `runner_generator_*` (9 tests) |
| Future Execution | - | - | `runner_future_*` (5 tests), `runner_async_*` (3 tests) |
| Parity Tests | - | - | `parity_generator_*`, `parity_future_*` |

### Key Test Files

- `src/compiler/src/mir/generator.rs` - MIR transform unit tests
- `src/runtime/src/value/async_gen.rs` - Runtime unit tests
- `src/driver/tests/runner_tests.rs` - System tests

### Parity Testing Strategy

Parity tests ensure compiled code produces the same results as interpreted code:

```rust
// Example parity test structure
#[test]
fn parity_generator_basic_sequence() {
    let source = r#"
fn* counter():
    yield 1
    yield 2
    yield 3

main = fn():
    let gen = counter()
    let a = next(gen)
    let b = next(gen)
    let c = next(gen)
    return a + b + c  // Should be 6
"#;

    // Run via interpreter
    let interp_result = run_interpreted(source);

    // Run via compiled code
    let compiled_result = run_compiled(source);

    assert_eq!(interp_result, compiled_result);
}
```

---

## Remaining Gaps and Future Work

### Feature 103 Gaps

1. **True Async Executor**: Current futures execute eagerly. Need async runtime integration for non-blocking execution.

2. **GC Safety Across Yields**: Generator frame slots store `RuntimeValue` but lack proper GC root registration between yields.

3. **Complex Pattern Matching**: Tuple, struct, or patterns, and guard patterns have limited codegen support.

4. **Inline Await in Generators**: Combining `await` inside generator bodies is not yet supported.

### Performance Optimization Opportunities

1. **Escape Analysis**: Avoid heap allocation for objects that don't escape function scope.

2. **Inline Caching**: Cache method lookups for virtual dispatch.

3. **Register Allocation**: Current naive allocation could be improved with graph coloring.

4. **Loop Optimizations**: Add support for loop invariant code motion and strength reduction.

---

---

Next: [Implementation Tutorial](codegen_technical_impl.md)
