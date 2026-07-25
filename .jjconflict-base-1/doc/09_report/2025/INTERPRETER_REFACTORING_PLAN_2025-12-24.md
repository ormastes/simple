# Interpreter Files Refactoring Plan
**Date:** 2025-12-24
**Status:** Analysis Complete - Implementation Pending
**Objective:** Refactor 4 large interpreter files (5,913 total lines) into modular sub-1000-line files

## Current State

### Files to Refactor
| File | Lines | Status |
|------|-------|--------|
| `interpreter_call.rs` | 1,861 | ❌ Too large |
| `interpreter_method.rs` | 1,455 | ❌ Too large |
| `interpreter_expr.rs` | 1,328 | ❌ Too large |
| `interpreter_macro.rs` | 1,269 | ❌ Too large |
| **Total** | **5,913** | |

## Refactoring Strategy

### 1. interpreter_call.rs (1,861 lines) → 4 modules

**Target Structure:**
```
interpreter_call/
├── mod.rs                (~200 lines) - Main dispatcher
├── builtins.rs          (~600 lines) - Built-in functions
├── bdd.rs               (~500 lines) - BDD testing framework
├── mock.rs              (~300 lines) - Mock library
└── core.rs              (~260 lines) - Core execution logic
```

**Content Distribution:**

**`builtins.rs` (~600 lines):**
- `range`, `Some`, `None`, `Ok`, `Err` constructors
- `send`, `recv`, `reply`, `join` (actor primitives)
- `spawn`, `spawn_isolated`, `async`, `future`
- `async_mode`, `async_workers`, `poll_future`, `poll_all_futures`
- `generator`, `next`, `collect`
- `ThreadPool` constructor
- Lines: 127-360 (built-ins section)

**`bdd.rs` (~500 lines):**
- BDD thread-local state (Lines 3-31)
- `describe`, `context`, `it`, `skip`
- `expect` assertion
- `shared_examples`, `it_behaves_like`, `include_examples`
- `before_each`, `after_each` hooks
- `context_def`, `given`, `given_lazy`, `let_lazy`
- `get_let`, `has_let` accessors
- Helper functions: `build_expect_failure_message`, `format_value_for_message`
- Lines: 3-762 (BDD infrastructure)

**`mock.rs` (~300 lines):**
- Mock/Spy matchers: `mock`, `spy`, `any`, `eq`, `be`
- Comparison matchers: `be_gt`, `be_lt`, `be_nil`, `be_empty`
- String matchers: `include`, `start_with`, `end_with`, `contains`
- Numeric matchers: `gt`, `lt`, `gte`, `lte`
- Type matcher: `of_type`
- Lines: 764-894 (mock library section)

**`core.rs` (~260 lines):**
- `bind_args`, `bind_args_with_injected`, `bind_args_with_values`
- `exec_lambda`
- `exec_function`, `exec_function_with_values`, `exec_function_with_captured_env`
- `exec_function_inner`, `exec_function_with_values_inner`
- Lines: 1055-1481 (core function execution)

**`mod.rs` (~200 lines):**
- Main `evaluate_call` dispatcher
- Enum variant constructors
- Associated function calls
- Generic type constructors (Channel)
- Lambda/closure calls
- Re-exports from submodules

### 2. interpreter_method.rs (1,455 lines) → 4 modules

**Target Structure:**
```
interpreter_method/
├── mod.rs                (~150 lines) - Main dispatcher
├── primitives.rs         (~400 lines) - Int, Float, Bool
├── collections.rs        (~600 lines) - Array, Tuple, Dict
└── special.rs            (~305 lines) - Option, Result, Unit, others
```

**Content Distribution:**

**`primitives.rs` (~400 lines):**
- **Int methods** (Lines 44-114):
  - `abs`, `sign`, `signum`, `is_positive`, `is_negative`, `is_zero`
  - `is_even`, `is_odd`, `to_float`, `to_string`
  - `clamp`, `min`, `max`, `pow`
  - `bit_count`, `leading_zeros`, `trailing_zeros`
  - `to_hex`, `to_bin`, `to_oct`
  - `times`, `up_to`, `down_to`

- **Float methods** (Lines 118-203):
  - `abs`, `sign`, `signum`, `is_positive`, `is_negative`, `is_zero`
  - `is_nan`, `is_infinite`, `is_finite`
  - `to_int`, `truncate`, `to_string`
  - `floor`, `ceil`, `round`, `trunc`, `fract`
  - `sqrt`, `cbrt`, `exp`, `exp2`, `ln`, `log2`, `log10`
  - `sin`, `cos`, `tan`, `asin`, `acos`, `atan`
  - `sinh`, `cosh`, `tanh`
  - `clamp`, `min`, `max`, `pow`, `powf`, `powi`
  - `log`, `atan2`, `hypot`
  - `to_degrees`, `to_radians`, `round_to`

- **Bool methods** (Lines 312-339):
  - `to_int`, `to_string`, `then`, `then_else`

**`collections.rs` (~600 lines):**
- **Array methods** (Lines 342-676):
  - Basic: `len`, `is_empty`, `first`, `last`, `get`, `contains`
  - Mutation: `push`, `append`, `pop`, `concat`, `extend`, `insert`, `remove`
  - Transformation: `reverse`, `slice`, `map`, `filter`, `reduce`, `fold`
  - Search: `find`, `any`, `all`, `index_of`
  - Aggregation: `join`, `sum`, `min`, `max`, `count`
  - Sorting: `sort`, `sort_desc`
  - Iteration: `enumerate`, `zip`, `flat_map`, `flatten`
  - Partitioning: `take`, `skip`, `drop`, `take_while`, `skip_while`, `drop_while`
  - Grouping: `chunk`, `chunks`, `unique`, `distinct`, `partition`, `group_by`

- **Tuple methods** (Lines 680-745):
  - `len`, `is_empty`, `get`, `first`, `last`
  - `to_array`, `contains`, `index_of`, `reverse`
  - `map`, `zip`, `enumerate`

- **Dict methods** (Lines 748-810):
  - `len`, `is_empty`, `contains_key`, `get`
  - `keys`, `values`, `entries`, `items`
  - `set`, `insert`, `remove`, `delete`
  - `merge`, `extend`, `get_or`
  - `map_values`, `filter`

**`special.rs` (~305 lines):**
- **Unit methods** (Lines 206-309):
  - `value`, `suffix`, `family`, `to_string`
  - Dynamic conversion: `to_X()` methods with SI prefix support

- **String methods** (via include, Lines 814):
  - Extracted to separate file `interpreter_method_string.rs`

- **Option methods** (Lines 817-916):
  - `is_some`, `is_none`, `unwrap`, `expect`
  - `unwrap_or`, `unwrap_or_else`, `or`, `ok_or`
  - `map`, `and_then`, `or_else`, `filter`
  - `flatten`, `take`

- **Result methods** (Lines 919-1043):
  - `is_ok`, `is_err`, `unwrap`, `expect`
  - `unwrap_or`, `unwrap_or_else`
  - `unwrap_err`, `expect_err`
  - `ok`, `err`, `or`
  - `map`, `map_err`, `and_then`, `or_else`, `flatten`

- **TraitObject, Future, Channel, ThreadPool** (Lines 1059-1163)

- **Mock methods** (Lines 1212-1328):
  - Configuration: `when`, `withArgs`, `with_args`
  - Stubbing: `returns`, `returnsOnce`, `returns_once`
  - Verification: `verify`, `called`, `calledTimes`, `called_times`
  - `calledWith`, `called_with`, `reset`, `getCalls`, `get_calls`

**`mod.rs` (~150 lines):**
- Main `evaluate_method_call` dispatcher
- Module-style dot calls
- BDD assertion methods (`to`, `not_to`)
- Dispatch to type-specific modules
- `evaluate_method_call_with_self_update` for mutations

### 3. interpreter_expr.rs (1,328 lines) → 3 modules

**Target Structure:**
```
interpreter_expr/
├── mod.rs                (~300 lines) - Main evaluator & dispatcher
├── values.rs             (~400 lines) - Literals, identifiers, simple values
├── operations.rs         (~400 lines) - Binary/unary ops, unit handling
└── complex.rs            (~228 lines) - Collections, comprehensions, patterns
```

**Content Distribution:**

**`values.rs` (~400 lines):**
- **Literals** (Lines 209-296):
  - `Integer`, `TypedInteger` (with unit suffix)
  - `Float`, `TypedFloat` (with unit suffix)
  - `Bool`, `Nil`
  - `String`, `TypedString` (with unit suffix)
  - `FString` (formatted strings)
  - `Symbol`

- **Identifiers** (Lines 287-331):
  - Variable lookup
  - Function references
  - Class constructors
  - Moved variable checking
  - Typo suggestions

- **Pointers** (Lines 332-350):
  - `New` expressions (Unique, Shared, Weak, Handle, Borrow, BorrowMut)

- **Ranges** (Lines 940-954):
  - `Range` with inclusive/exclusive bounds

**`operations.rs` (~400 lines):**
- **Unit helpers** (Lines 1-196):
  - `lookup_unit_family`, `lookup_unit_family_with_si`
  - `evaluate_unit_binary_inner` (arithmetic on units)
  - `evaluate_unit_unary_inner` (unary ops on units)

- **Binary operations** (Lines 351-563):
  - Unit type safety checking
  - Arithmetic: `Add`, `Sub`, `Mul`, `Div`, `Mod`, `Pow`, `FloorDiv`
  - Comparison: `Eq`, `NotEq`, `Lt`, `Gt`, `LtEq`, `GtEq`, `Is`
  - Logical: `And`, `Or`
  - Bitwise: `BitAnd`, `BitOr`, `BitXor`, `ShiftLeft`, `ShiftRight`
  - Membership: `In`

- **Unary operations** (Lines 564-614):
  - `Neg`, `Not`, `BitNot`
  - `Ref`, `RefMut`, `Deref`
  - Unit type safety for unary ops

**`complex.rs` (~228 lines):**
- **Lambda** (Lines 615-634):
  - Closure creation with move semantics

- **Control flow** (Lines 635-720):
  - `If` expressions
  - `Match` expressions with exhaustiveness checking

- **Collections** (Lines 916-997):
  - `Array`, `Tuple`, `Dict`
  - Spread operators

- **Indexing** (Lines 998-1077):
  - `Index`, `TupleIndex`
  - Slicing

- **Comprehensions** (Lines 1078-1115):
  - `ListComprehension`
  - `DictComprehension`

- **Concurrency** (Lines 1181-1223):
  - `Spawn`, `Await`, `Yield`

- **Special** (Lines 1248-1302):
  - `Try` operator (?)
  - Contract expressions
  - `DoBlock`
  - `Cast` expressions

**`mod.rs` (~300 lines):**
- Main `evaluate_expr` function (dispatcher)
- `Call` and `MethodCall` delegation
- `FieldAccess` and property access
- `StructInit`, `Path` (enum variants)
- `FunctionalUpdate`
- `MacroInvocation`

### 4. interpreter_macro.rs (1,269 lines) → 3 modules

**Target Structure:**
```
interpreter_macro/
├── mod.rs                (~100 lines) - Main entry point
├── builtins.rs           (~160 lines) - Built-in macros
├── hygiene.rs            (~600 lines) - Hygiene transformations
└── expansion.rs          (~409 lines) - User macro expansion
```

**Content Distribution:**

**`builtins.rs` (~160 lines):**
- Built-in macro implementations (Lines 26-159):
  - `println`, `print`, `vec`
  - `assert`, `assert_eq`, `assert_unit`
  - `panic`, `format`, `dbg`

**`hygiene.rs` (~600 lines):**
- `MacroHygieneContext` struct (Lines 249-290)
- `apply_macro_hygiene_block` (Lines 292-311)
- `apply_macro_hygiene_node` (Lines 313-520)
- `apply_macro_hygiene_expr` (Lines 522-801)
- `apply_macro_hygiene_pattern` (Lines 803-873)

**`expansion.rs` (~409 lines):**
- Thread-local state (Lines 6-15):
  - `MACRO_INTRODUCED_SYMBOLS`
  - `take_macro_introduced_symbols`

- User macro expansion (Lines 162-247):
  - `expand_user_macro`
  - Macro validation
  - Contract processing
  - Statement execution (ConstEval, Emit, Stmt)

- Template substitution (Lines 875-1269):
  - `build_macro_const_bindings`
  - `const_value_to_string`
  - `substitute_block_templates`
  - `substitute_node_templates`
  - `substitute_expr_templates`
  - `substitute_template_string`

**`mod.rs` (~100 lines):**
- Main `evaluate_macro_invocation` function
- Dispatch to built-ins or user macros
- Re-exports

## Implementation Steps

### Phase 1: Extract Helper Modules (Low Risk)
1. Create `interpreter_call_builtins.rs` with built-in functions ✅
2. Create `interpreter_call_mock.rs` with mock library
3. Create `interpreter_method_primitives.rs` with Int/Float/Bool methods
4. Create `interpreter_method_collections.rs` with Array/Tuple/Dict methods
5. Create `interpreter_expr_values.rs` with literals and identifiers
6. Create `interpreter_expr_operations.rs` with binary/unary ops
7. Create `interpreter_macro_builtins.rs` with built-in macros
8. Create `interpreter_macro_hygiene.rs` with hygiene logic

### Phase 2: Extract Core Logic (Medium Risk)
1. Create `interpreter_call_bdd.rs` with BDD framework
2. Create `interpreter_call_core.rs` with function execution
3. Create `interpreter_method_special.rs` with Option/Result/Unit
4. Create `interpreter_expr_complex.rs` with collections/comprehensions
5. Create `interpreter_macro_expansion.rs` with expansion logic

### Phase 3: Create Dispatcher Modules (High Risk)
1. Create `interpreter_call/mod.rs` dispatcher
2. Create `interpreter_method/mod.rs` dispatcher
3. Create `interpreter_expr/mod.rs` dispatcher
4. Create `interpreter_macro/mod.rs` dispatcher

### Phase 4: Update Main Files
1. Replace `interpreter_call.rs` with `interpreter_call/` directory
2. Replace `interpreter_method.rs` with `interpreter_method/` directory
3. Replace `interpreter_expr.rs` with `interpreter_expr/` directory
4. Replace `interpreter_macro.rs` with `interpreter_macro/` directory

### Phase 5: Testing & Validation
1. Run `cargo build` to verify compilation
2. Run `cargo test --workspace` to verify functionality
3. Run `cargo clippy` to check for warnings
4. Verify no regressions in existing tests

## Expected Results

### Before Refactoring
| File | Lines |
|------|-------|
| `interpreter_call.rs` | 1,861 |
| `interpreter_method.rs` | 1,455 |
| `interpreter_expr.rs` | 1,328 |
| `interpreter_macro.rs` | 1,269 |
| **Total** | **5,913** |

### After Refactoring
| Module | Files | Max Lines | Total Lines |
|--------|-------|-----------|-------------|
| `interpreter_call/` | 5 | ~600 | ~1,860 |
| `interpreter_method/` | 4 | ~600 | ~1,455 |
| `interpreter_expr/` | 4 | ~400 | ~1,328 |
| `interpreter_macro/` | 4 | ~600 | ~1,269 |
| **Total** | **17** | **~600** | **~5,912** |

**Improvements:**
- ✅ All files under 1,000 lines
- ✅ Most files under 700 lines
- ✅ Logical organization by functionality
- ✅ Easier to navigate and maintain
- ✅ Better separation of concerns
- ✅ Improved testability

## Dependencies & Considerations

### Module Dependencies
- All submodules will depend on:
  - `crate::value::*`
  - `crate::error::CompileError`
  - `simple_parser::ast::*`
  - `std::collections::HashMap`

### Circular Dependency Risks
- **interpreter_call** calls **interpreter_expr** (via `evaluate_expr`)
- **interpreter_expr** calls **interpreter_call** (via `evaluate_call` in `Call` expressions)
- **Solution:** Keep main dispatchers (`evaluate_expr`, `evaluate_call`) in top-level modules

### Include Files
- `interpreter_call.rs` includes `interpreter_call_block_execution.rs` (Line 1277)
- `interpreter_method.rs` includes `interpreter_method_string.rs` (Line 814)
- `interpreter_expr.rs` includes `interpreter_expr_casting.rs` (Line 1)
- These will need to be integrated into the new module structure

## Risk Assessment

### Low Risk (Helper Extraction)
- ✅ Built-in functions (isolated, no internal dependencies)
- ✅ Mock library (isolated, clear boundaries)
- ✅ Primitives methods (self-contained)
- ✅ Collections methods (self-contained)

### Medium Risk (Core Logic)
- ⚠️ BDD framework (thread-local state, complex interactions)
- ⚠️ Function execution (calls many helpers)
- ⚠️ Macro hygiene (complex transformations)

### High Risk (Dispatcher Refactoring)
- ⛔ Main expression evaluator (circular dependencies)
- ⛔ Main call evaluator (complex dispatch logic)
- ⛔ Main method dispatcher (dynamic dispatch)

## Rollback Plan

If compilation fails or tests break:
1. Keep original files as `.backup`
2. Restore from backup
3. Identify specific module causing issues
4. Fix incrementally
5. Re-test after each fix

## Next Steps

1. Review this plan with the team
2. Get approval for refactoring approach
3. Create feature branch: `refactor/interpreter-files-split`
4. Implement Phase 1 (low-risk extractions)
5. Test after each phase
6. Merge when all tests pass

## Notes

- This refactoring is **purely structural** - no logic changes
- All existing functionality must be preserved
- All tests must continue to pass
- Code coverage should remain the same
- Performance should not be impacted (all inlined by compiler)

---

**Analysis completed:** 2025-12-24
**Ready for implementation:** Yes
**Estimated effort:** 4-6 hours
**Risk level:** Medium (with proper testing)
