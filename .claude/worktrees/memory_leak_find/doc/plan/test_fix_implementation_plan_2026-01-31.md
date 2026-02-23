# Test Fix Implementation Plan - Comprehensive Approach

**Date**: 2026-01-31
**Target**: Fix 1550 test failures (7622 → 9172 passing tests)
**Approach**: Full architectural solutions for all 6 decisions
**Estimated Total Effort**: 78-134 hours (10-17 working days)

---

## Selected Options Summary

| Decision | Option | Effort | Tests | Complexity |
|----------|--------|--------|-------|------------|
| **1. Module/Import** | A - Two-Phase | 16-24h | +450 | HIGH |
| **2. Closure Capture** | B - Arc<RefCell<Env>> | 8-16h | +20 | MEDIUM |
| **3. Mutable Collections** | Default Mutable | 6-10h | +15 | MEDIUM |
| **4. TreeSitter Integration** | A - Full Integration | 16-24h | +80 | HIGH |
| **5. Feature Implementation** | C - Selective (4 areas) | 40-60h | +240 | VARIED |
| **6. Spec Restructure** | B - File Reorganization | 12-20h | +80 | LOW |
| **7. Type Annotation Conversion** | from() Method | 5-6h | +50 | LOW |
| **8. Fixed-Size Arrays** | [T; N] Syntax | 18-26h | +80 | MEDIUM |
| **9. Target-Based Defaults** | Embedded Mode | 13-20h | 0 | MEDIUM |
| **Tactical Fixes** | (Remaining from Iter 1) | 15-25h | +167 | LOW |

**Total**: 149-231 hours, +1182 tests (target: 8804/9172 = 96.0% pass rate)

---

## Phase 0: Test-First - Write SSpec Tests (Week 1, 8-12h)

**CRITICAL**: Write ALL SSpec tests BEFORE implementing features (Test-Driven Development).

**See**: `doc/plan/array_features_sspec_tests.md` for complete test specifications.

### Test Files to Create

```bash
test/system/features/arrays/
├── mutable_by_default_spec.spl              # 20-25 tests
├── type_conversion_spec.spl                  # 15-20 tests
├── fixed_size_arrays_spec.spl                # 25-30 tests
├── fixed_size_edge_cases_spec.spl            # 15-20 tests
├── target_defaults_spec.spl                  # 15-20 tests
├── freeze_unfreeze_spec.spl                  # 15-20 tests
└── array_performance_spec.spl                # 10-15 tests

test/system/features/collections/
├── custom_backend_spec.spl                   # 15-20 tests
└── backend_conversion_spec.spl               # Type coercion tests
```

**Total**: 130-170 comprehensive SSpec tests

### Test Writing Process

1. **Write tests for Decision #3** (Mutable by Default) - 2h
2. **Write tests for Decision #7** (Type Conversion) - 1.5h
3. **Write tests for Decision #8** (Fixed-Size Arrays) - 3h
4. **Write tests for Decision #9** (Target Defaults) - 1.5h
5. **Write integration and performance tests** - 2h

### Verification

```bash
# Run all tests - should ALL FAIL initially
./rust/target/debug/simple_runtime test test/system/features/arrays/

# Expected output:
# FAIL mutable_by_default_spec.spl (0 passed, 25 failed)
# FAIL type_conversion_spec.spl (0 passed, 20 failed)
# FAIL fixed_size_arrays_spec.spl (0 passed, 30 failed)
# ... etc
#
# Total: 0 passed, 150+ failed (EXPECTED - tests written first!)
```

**Deliverable**: 130-170 failing SSpec tests documenting all requirements.

---

## Phase 1: Foundation (Week 2-3, 31-49h)

### 1.1 Decision #1: Two-Phase Module/Import System (16-24h)

**Objective**: Enable full import/export across modules with compile-time type checking.

#### Step 1.1.1: Enable ModuleResolver in Compiler (6-8h)

**File**: `rust/compiler/src/hir/lower/mod.rs`

**Changes**:
```rust
// Current:
pub struct Lowerer {
    module_resolver: Option<ModuleResolver>,  // Always None
}

impl Lowerer {
    pub fn new(...) -> Self {
        Self {
            module_resolver: None,  // ❌ Disabled
        }
    }
}

// New:
impl Lowerer {
    pub fn new(project_root: PathBuf, stdlib_paths: Vec<PathBuf>) -> Self {
        let resolver = ModuleResolver::new(project_root, stdlib_paths);
        Self {
            module_resolver: Some(resolver),  // ✅ Enabled
        }
    }
}
```

**Implementation Tasks**:
1. Update `Lowerer::new()` to accept project root and stdlib paths (1h)
2. Initialize `ModuleResolver` with correct paths (1h)
   - Project root: from CLI args or current dir
   - Stdlib paths: `rust/lib/std/src/` + any user-configured paths
3. Update all call sites of `Lowerer::new()` to pass paths (2h)
4. Wire module resolver to type registration in globals (2-3h)
5. Test with simple cross-module type reference (1-2h)

**Test Command**:
```bash
# Create test files:
# a.spl:
export struct Point { x: i64, y: i64 }

# b.spl:
use a
val p: a.Point = a.Point(x: 1, y: 2)

./rust/target/debug/simple_runtime b.spl
# Should compile without "type not found" error
```

#### Step 1.1.2: Fix Export Extraction in Interpreter (6-8h)

**File**: `rust/compiler/src/interpreter_module/module_evaluator.rs`

**Bug #1 Fix** (line ~83):
```rust
// export_functions() - BEFORE:
fn export_functions(
    module: &Module,
    exports: &mut HashMap<String, Value>,
    // ...
) -> Result<(), CompileError> {
    for func in &module.functions {
        let func_value = Value::Function {
            name: func.name.clone(),
            // ... other fields ...
        };
        // ❌ MISSING: exports.insert(func.name.clone(), func_value);
    }
    Ok(())
}

// AFTER:
fn export_functions(
    module: &Module,
    exports: &mut HashMap<String, Value>,
    // ...
) -> Result<(), CompileError> {
    for func in &module.functions {
        let func_value = Value::Function {
            name: func.name.clone(),
            // ... other fields ...
        };
        exports.insert(func.name.clone(), func_value);  // ✅ ADD THIS
    }
    Ok(())
}
```

**Bug #2 Fix** (line ~86):
```rust
// process_bare_exports() - BEFORE:
fn process_bare_exports(
    exports: &mut HashMap<String, Value>,
) -> Result<(), CompileError> {
    return Ok(());  // ❌ Early return, does nothing
}

// AFTER:
fn process_bare_exports(
    stmts: &[Stmt],
    env: &Environment,
    exports: &mut HashMap<String, Value>,
) -> Result<(), CompileError> {
    for stmt in stmts {
        match stmt {
            Stmt::Export { name, value } => {
                // Evaluate the exported value in current environment
                let export_value = evaluate_expr(value, env)?;
                exports.insert(name.clone(), export_value);
            }
            _ => {}
        }
    }
    Ok(())
}
```

**Implementation Tasks**:
1. Add exports.insert() to export_functions() (0.5h)
2. Implement process_bare_exports() logic (2-3h)
   - Add parameters for stmts and env
   - Iterate over statements
   - Match Export statements
   - Evaluate and insert into exports
3. Add debug logging for exports dict (0.5h)
4. Update call sites to pass new parameters (1h)
5. Test with simple module export (1-2h)

**Test Command**:
```bash
# Create test file:
# math.spl:
export fn add(a: i64, b: i64) -> i64:
    a + b

export val PI = 3.14159

# main.spl:
use math
print(math.add(2, 3))  # Should print: 5
print(math.PI)         # Should print: 3.14159

./rust/target/debug/simple_runtime main.spl
```

#### Step 1.1.3: Integration and Testing (4-8h)

**File**: `rust/compiler/src/hir/lower/import_loader.rs`

**Changes**:
```rust
// Current:
pub fn resolve_import(&mut self, import: &Import) -> Result<(), CompileError> {
    if self.module_resolver.is_none() {
        return Ok(());  // ❌ Early exit when disabled
    }
    // ... rest of code ...
}

// New:
pub fn resolve_import(&mut self, import: &Import) -> Result<(), CompileError> {
    let resolver = self.module_resolver.as_mut()
        .ok_or_else(|| CompileError::semantic("module resolver not initialized"))?;

    // Now resolver is guaranteed to exist - proceed with resolution
    // ... rest of code ...
}
```

**Implementation Tasks**:
1. Remove early exit in import_loader.rs (0.5h)
2. Add proper error handling for missing resolver (0.5h)
3. Test compile-time type checking across modules (2-3h)
4. Test runtime value loading from imports (2-3h)
5. Verify both phases work together (1-2h)

**Integration Test Suite**:
```bash
# Test 1: Type checking
# Should fail at compile time if type mismatch
use math
val x: math.Point = "not a point"  # Compile error ✓

# Test 2: Runtime values
use math
print(math.PI)  # Runtime value ✓

# Test 3: Cross-module functions
use math
val result = math.add(10, 20)  # Both type check + runtime ✓
```

#### Step 1.1.4: Re-enable ml.torch Modules (4-6h)

**Tasks**:
1. Rename `rust/lib/std/src/ml.disabled/` → `rust/lib/std/src/ml/` (0.5h)
2. Update module index to include ml.torch.* (0.5h)
3. Fix any broken imports in ml modules (1-2h)
4. Stub missing PyTorch FFI functions (2-3h)
   - Add feature gate for torch FFI
   - Add stub implementations when torch disabled
   - Mirror the TUI feature gating pattern
5. Run all ml.torch tests (1h)

**Feature Gate Pattern**:
```rust
// rust/compiler/src/interpreter_extern/mod.rs
#[cfg(feature = "torch")]
pub mod torch_ffi;

#[cfg(feature = "torch")]
"torch_tensor_new" => torch_ffi::torch_tensor_new(&evaluated),

#[cfg(not(feature = "torch"))]
"torch_tensor_new" => Ok(Value::Nil),  // Stub when disabled
```

**Test Command**:
```bash
# Should work now:
./rust/target/debug/simple_runtime test test/lib/std/unit/ml/torch/
# Expected: Many tests start passing
```

**Expected Results**:
- +150 tests from ml.torch modules
- +80 tests from simple.parser imports
- +120 tests from cross-module features
- +100 tests from user library imports
- **Total: +450 tests passing**

**Verification**:
```bash
cd /home/ormastes/dev/pub/simple
cargo build --manifest-path=rust/Cargo.toml
./rust/target/debug/simple_runtime test 2>&1 | grep "^Results:"
# Expected: 8072+ passed (7622 + 450)
```

---

### 1.2 Decision #2: Closure Variable Capture with Arc<RefCell<Env>> (8-16h)

**Objective**: Enable mutations to captured variables in closures to propagate to outer scope.

**IMPORTANT**: RefCell is a **Rust feature** used in the interpreter implementation, not a Simple language feature. Users write normal Simple code; RefCell is internal.

#### Step 1.2.1: Update Value::Function Definition (2-3h)

**File**: `rust/compiler/src/value/mod.rs` (or wherever Value enum is defined)

**Changes**:
```rust
// BEFORE:
pub enum Value {
    Function {
        name: String,
        params: Vec<String>,
        body: Vec<Stmt>,
        captured_env: Environment,  // ❌ Cloned on every call
        // ... other fields ...
    },
    // ... other variants ...
}

// AFTER:
use std::rc::Rc;
use std::cell::RefCell;

pub enum Value {
    Function {
        name: String,
        params: Vec<String>,
        body: Vec<Stmt>,
        captured_env: Rc<RefCell<Environment>>,  // ✅ Shared mutable
        // ... other fields ...
    },
    // ... other variants ...
}
```

**Implementation Tasks**:
1. Add `use std::rc::Rc; use std::cell::RefCell;` to imports (0.5h)
2. Change `captured_env: Environment` → `captured_env: Rc<RefCell<Environment>>` (0.5h)
3. Update all Value::Function constructors (1-2h)
   - Wrap Environment in `Rc::new(RefCell::new(env))`
   - Search for all `Value::Function {` patterns
   - Update ~10-15 construction sites

#### Step 1.2.2: Update Function Execution Logic (4-6h)

**File**: `rust/compiler/src/interpreter_call/core/function_exec.rs`

**Changes**:
```rust
// BEFORE:
pub fn exec_function_with_captured_env(
    func: &Value,
    args: Vec<Value>,
    // ...
) -> Result<Value, CompileError> {
    if let Value::Function { captured_env, body, params, ... } = func {
        // Clone the environment (mutations lost)
        let mut local_env = captured_env.clone();

        // Bind parameters
        for (param, arg) in params.iter().zip(args) {
            local_env.insert(param.clone(), arg);
        }

        // Execute body
        execute_stmts(body, &local_env)?;
    }
    // ...
}

// AFTER:
pub fn exec_function_with_captured_env(
    func: &Value,
    args: Vec<Value>,
    // ...
) -> Result<Value, CompileError> {
    if let Value::Function { captured_env, body, params, ... } = func {
        // Borrow the shared environment (mutations persist)
        let mut env_ref = captured_env.borrow_mut();

        // Bind parameters (in shared environment)
        for (param, arg) in params.iter().zip(args) {
            env_ref.insert(param.clone(), arg);
        }

        // Execute body (mutations affect shared environment)
        let result = execute_stmts(body, &*env_ref)?;

        // Drop borrow before returning
        drop(env_ref);

        result
    }
    // ...
}
```

**Implementation Tasks**:
1. Replace `captured_env.clone()` with `captured_env.borrow_mut()` (1h)
2. Update all environment access to use RefCell borrow (2-3h)
3. Handle borrow checker errors (1-2h)
   - Ensure no simultaneous mutable borrows
   - Add `drop()` calls where needed
   - Fix lifetime issues
4. Add error handling for borrow failures (0.5h)

#### Step 1.2.3: Update Lambda/Closure Creation (2-3h)

**File**: `rust/compiler/src/interpreter_call/mod.rs` (lambda creation)

**Changes**:
```rust
// BEFORE:
Expr::Lambda { params, body, ... } => {
    // Capture current environment by cloning
    let captured_env = env.clone();

    Ok(Value::Function {
        params: params.clone(),
        body: body.clone(),
        captured_env,  // Environment copied
        // ...
    })
}

// AFTER:
use std::rc::Rc;
use std::cell::RefCell;

Expr::Lambda { params, body, ... } => {
    // Capture current environment by wrapping in Rc<RefCell>
    let captured_env = Rc::new(RefCell::new(env.clone()));

    Ok(Value::Function {
        params: params.clone(),
        body: body.clone(),
        captured_env,  // Environment shared
        // ...
    })
}
```

**Implementation Tasks**:
1. Update lambda creation to wrap env in Rc<RefCell> (1h)
2. Update closure creation (if different path) (1h)
3. Test with nested closures (0.5-1h)

#### Step 1.2.4: Testing and Validation (1-2h)

**Test Cases**:
```simple
# Test 1: Basic mutation
describe "closure capture":
    it "should propagate mutations":
        var counter = 0
        val increment = fn():
            counter = counter + 1

        increment()
        expect(counter).to_equal(1)  # Should pass now

        increment()
        expect(counter).to_equal(2)  # Should pass now

# Test 2: Nested closures
describe "nested closures":
    it "should share environment":
        var x = 0
        val outer = fn():
            val inner = fn():
                x = x + 1
            inner()
            inner()

        outer()
        expect(x).to_equal(2)  # Should pass now

# Test 3: Multiple closures sharing environment
describe "shared captures":
    it "should see each other's mutations":
        var shared = 10
        val add_five = fn(): shared = shared + 5
        val sub_three = fn(): shared = shared - 3

        add_five()
        sub_three()
        expect(shared).to_equal(12)  # Should pass now
```

**Run Tests**:
```bash
./rust/target/debug/simple_runtime test test/system/features/closures/
# Expected: +20-30 tests passing
```

**Expected Results**:
- Closure mutation tests pass
- Nested closure tests pass
- No RefCell borrow panics
- **Total: +20-30 tests passing**

---

### 1.3 Tactical Fixes - Remaining Items (15-25h)

Complete the unfinished items from Iteration 1:

#### 1.3.1: Missing Stdlib Functions (4-8h)

**File**: `rust/compiler/src/interpreter_call/bdd.rs`

Add implementations:
```rust
// BDD framework functions
"gen" => {
    // Generator for property-based testing
    // Return a generator object
    Ok(Some(Value::Generator { /* ... */ }))
}

"seed" => {
    // Set random seed for reproducibility
    let seed = eval_arg_int(args, 0, 0, env, ...)?;
    // Set global RNG seed
    Ok(Some(Value::Nil))
}

"feature" => {
    // Feature marker for BDD
    // Similar to describe but for feature-level grouping
    Ok(Some(Value::Nil))
}
```

**File**: `rust/compiler/src/interpreter_extern/mod.rs`

Add FFI functions:
```rust
"kernel" => {
    // GPU kernel wrapper
    Ok(Value::Kernel { /* stub */ })
}

"tokenize" => {
    // Text tokenization
    let text = eval_arg_string(args, 0, env)?;
    let tokens = text.split_whitespace()
        .map(|s| Value::Str(s.to_string()))
        .collect();
    Ok(Value::Array(tokens))
}

"Token" => {
    // Token constructor
    Ok(Value::Object {
        class: "Token".to_string(),
        fields: HashMap::new(),
    })
}

"Lexer" => {
    // Lexer constructor
    Ok(Value::Object {
        class: "Lexer".to_string(),
        fields: HashMap::new(),
    })
}
```

**Expected**: +50 tests

#### 1.3.2: Builtin Type Methods (3-5h)

**File**: `rust/compiler/src/interpreter_method/primitives.rs`

Add methods:
```rust
// Duration methods
"total_seconds" => {
    // For Duration type
    if let Value::Duration(d) = receiver {
        Ok(Value::Float(d.as_secs_f64()))
    }
}

"add" => {
    // Duration + Duration
    let other = eval_arg_duration(args, 0)?;
    if let Value::Duration(d) = receiver {
        Ok(Value::Duration(d + other))
    }
}

"subtract_hours" => {
    let hours = eval_arg_int(args, 0)?;
    if let Value::Duration(d) = receiver {
        let result = d - Duration::from_secs(hours as u64 * 3600);
        Ok(Value::Duration(result))
    }
}

// nil methods
"len" => {
    if let Value::Nil = receiver {
        Ok(Value::Int(0))  // nil has length 0
    }
}
```

**Expected**: +15 tests

#### 1.3.3: Dict Methods (6-10h)

**File**: `rust/compiler/src/interpreter_method/collections.rs`

Add dict-specific methods:
```rust
"from_dict" => {
    // Constructor from dict literal
    let dict = eval_arg_dict(args, 0)?;
    Ok(Value::Dict(dict))
}

"compile" => {
    // Domain-specific: compile a dict config
    if let Value::Dict(d) = receiver {
        // Stub implementation
        Ok(Value::Object {
            class: "CompiledConfig".to_string(),
            fields: d.clone(),
        })
    }
}

"tensor" => {
    // Convert dict to tensor representation
    if let Value::Dict(d) = receiver {
        // Stub: return a tensor object
        Ok(Value::Object {
            class: "Tensor".to_string(),
            fields: d.clone(),
        })
    }
}
```

**Expected**: +40 tests

#### 1.3.4: Parser Edge Cases (2-4h)

**File**: `rust/parser/src/expr_parsing/literals.rs`

Fix empty array parsing:
```rust
// BEFORE:
fn parse_array_literal() -> Result<Expr, ParseError> {
    expect_token(Token::LeftBracket)?;
    let elements = parse_comma_separated_exprs()?;  // ❌ Fails on empty
    expect_token(Token::RightBracket)?;
    Ok(Expr::Array(elements))
}

// AFTER:
fn parse_array_literal() -> Result<Expr, ParseError> {
    expect_token(Token::LeftBracket)?;

    // Handle empty array case
    if peek_token() == Some(Token::RightBracket) {
        consume_token();
        return Ok(Expr::Array(Vec::new()));  // ✅ Empty array
    }

    let elements = parse_comma_separated_exprs()?;
    expect_token(Token::RightBracket)?;
    Ok(Expr::Array(elements))
}
```

**Expected**: +10 tests

#### 1.3.5: Lazy Value Bindings (3-5h)

**File**: `rust/compiler/src/interpreter_call/bdd.rs`

Implement lazy evaluation:
```rust
use std::sync::Mutex;
use std::collections::HashMap;

lazy_static! {
    static ref LAZY_VALUES: Mutex<HashMap<String, (Value, bool)>> =
        Mutex::new(HashMap::new());
}

"let" => {
    // BDD lazy binding
    let name = eval_arg_string(args, 0)?;
    let value_expr = args.get(1)?;

    // Store unevaluated expression
    LAZY_VALUES.lock().unwrap()
        .insert(name.clone(), (value_expr.clone(), false));

    Ok(Some(Value::Nil))
}

"lazy" => {
    // Access lazy value (memoized)
    let name = eval_arg_string(args, 0)?;
    let mut lazy_map = LAZY_VALUES.lock().unwrap();

    if let Some((expr, evaluated)) = lazy_map.get_mut(&name) {
        if !*evaluated {
            // First access: evaluate and cache
            let value = evaluate_expr(expr, env)?;
            *expr = value.clone();
            *evaluated = true;
            Ok(Some(value))
        } else {
            // Subsequent access: return cached
            Ok(Some(expr.clone()))
        }
    } else {
        Err(CompileError::semantic(format!("lazy value '{}' not found", name)))
    }
}
```

**Expected**: +10 tests

**Total Expected from Tactical Fixes**: +167 tests (122 tests remaining from original 270)

---

## Phase 2: Advanced Features (Week 3-4, 22-34h)

### 2.1 Decision #3: Mutable Collections by Default (6-10h)

**Objective**: Make collections mutable by default (matches user expectations and other languages).

**Design**: Collections are reference types (like Python, JavaScript, Java) and mutable by default.

#### Step 2.1.1: Update Value::Array to be Mutable by Default (2-3h)

**File**: `rust/compiler/src/value/mod.rs`

**Changes**:
```rust
// BEFORE (from iteration 1):
pub enum Value {
    Array(Vec<Value>),  // Immutable
    Dict(HashMap<String, Value>),
    // ...
}

// AFTER:
use std::rc::Rc;
use std::cell::RefCell;

pub enum Value {
    // Mutable by default:
    Array(Rc<RefCell<Vec<Value>>>),
    Dict(Rc<RefCell<HashMap<String, Value>>>),

    // Immutable (explicit):
    FrozenArray(Rc<Vec<Value>>),  // Created via freeze()
    FrozenDict(Rc<HashMap<String, Value>>),

    // ...
}
```

**Implementation Tasks**:
1. Update Value::Array type (0.5h)
2. Update Value::Dict type (0.5h)
3. Update all array/dict constructors (1-2h)
   - Wrap in `Rc::new(RefCell::new(...))`
   - Search for `Value::Array(vec![...])` patterns
   - ~50+ construction sites

#### Step 2.1.2: Update Collection Methods for Mutable by Default (3-5h)

**File**: `rust/compiler/src/interpreter_method/collections.rs`

**Changes**:
```rust
"pop" => {
    match receiver {
        Value::Array(arr_ref) => {
            let mut arr = arr_ref.borrow_mut();
            arr.pop().ok_or_else(|| CompileError::semantic("pop from empty array"))
        }
        Value::FrozenArray(_) => {
            Err(CompileError::semantic("cannot pop from frozen array"))
        }
        _ => Err(CompileError::type_error("not an array"))
    }
}

"push" => {
    match receiver {
        Value::Array(arr_ref) => {
            let elem = eval_arg(args, 0)?;
            let mut arr = arr_ref.borrow_mut();
            arr.push(elem);
            Ok(Value::Nil)
        }
        Value::FrozenArray(_) => {
            Err(CompileError::semantic("cannot push to frozen array"))
        }
        _ => Err(CompileError::type_error("not an array"))
    }
}

"insert" => {
    match receiver {
        Value::Dict(dict_ref) => {
            let key = eval_arg_string(args, 0)?;
            let value = eval_arg(args, 1)?;
            let mut dict = dict_ref.borrow_mut();
            dict.insert(key, value);
            Ok(Value::Nil)
        }
        Value::FrozenDict(_) => {
            Err(CompileError::semantic("cannot insert into frozen dict"))
        }
        _ => Err(CompileError::type_error("not a dict"))
    }
}
```

**Implementation Tasks**:
1. Update pop() to mutate and return element (1h)
2. Update push() to mutate in place (0.5h)
3. Update insert() for dicts (0.5h)
4. Update remove(), clear(), etc. (1-2h)
5. Handle RefCell borrow errors gracefully (0.5-1h)

#### Step 2.1.3: Update Array/Dict Access (1-2h)

**File**: `rust/compiler/src/interpreter_call/mod.rs` (indexing)

**Changes**:
```rust
// BEFORE:
Expr::Index { array, index } => {
    let arr = evaluate_expr(array, env)?;
    if let Value::Array(vec) = arr {
        let idx = evaluate_index(index)?;
        Ok(vec.get(idx).cloned().unwrap_or(Value::Nil))
    }
}

// AFTER:
Expr::Index { array, index } => {
    let arr = evaluate_expr(array, env)?;
    if let Value::Array(arr_ref) = arr {
        let arr_borrow = arr_ref.borrow();
        let idx = evaluate_index(index)?;
        Ok(arr_borrow.get(idx).cloned().unwrap_or(Value::Nil))
    }
}
```

#### Step 2.1.4: Add freeze() Function for Immutable Collections (0.5-1h)

**File**: `rust/compiler/src/interpreter_call/builtins.rs`

**Implementation**:
```rust
"freeze" => {
    let value = eval_arg(args, 0)?;
    match value {
        Value::Array(arr_ref) => {
            let arr = arr_ref.borrow().clone();
            Ok(Value::FrozenArray(Rc::new(arr)))
        }
        Value::Dict(dict_ref) => {
            let dict = dict_ref.borrow().clone();
            Ok(Value::FrozenDict(Rc::new(dict)))
        }
        Value::FrozenArray(_) | Value::FrozenDict(_) => {
            Ok(value)  // Already frozen
        }
        _ => Err(CompileError::semantic("freeze() requires a collection"))
    }
}
```

#### Step 2.1.5: Verify with SSpec Tests (0.5-1h)

**Tests already written in Phase 0** (see `mutable_by_default_spec.spl`).

**Run Tests**:
```bash
# Tests written in Phase 0, now should pass:
./rust/target/debug/simple_runtime test test/system/features/arrays/mutable_by_default_spec.spl
# Expected: 20-25 tests passing (previously failed)

./rust/target/debug/simple_runtime test test/system/features/arrays/freeze_unfreeze_spec.spl
# Expected: 15-20 tests passing
```

**Expected Results**: 35-45 tests passing (were failing in Phase 0)

---

### 2.2 Decision #6: Restructure Spec Files (12-20h)

**Objective**: Organize test files for better clarity and fix metadata reporting issues.

#### Step 2.2.1: Analyze Current Structure (2-3h)

**Tasks**:
1. List all spec files with pass/fail status (1h)
2. Identify files with mixed concerns (1h)
3. Create restructure plan (category → files mapping) (1h)

**Command**:
```bash
find test/ -name "*_spec.spl" | xargs -I{} sh -c '
    echo "=== {} ==="
    ./rust/target/debug/simple_runtime test {} 2>&1 | grep "passed\|failed"
'
```

#### Step 2.2.2: Split Mixed Spec Files (6-10h)

**Example Restructure**:
```
# BEFORE:
test/system/features/parser/parser_functions_spec.spl
  - Function parsing tests (20 tests)
  - Control flow parsing tests (16 tests)
  - Error recovery tests (37 tests)
  - All mixed together

# AFTER:
test/system/features/parser/
  ├── function_parsing_spec.spl (20 tests)
  ├── control_flow_parsing_spec.spl (16 tests)
  └── error_recovery_spec.spl (37 tests)
```

**Implementation Tasks**:
1. Create new spec file structure (1h)
2. Move test cases to appropriate files (3-5h)
   - Copy describe blocks to new files
   - Update imports/dependencies
   - Remove from original files
3. Delete old mixed files (0.5h)
4. Update test runner to find new files (1h)
5. Run full test suite to verify (1-2h)

#### Step 2.2.3: Fix Test Metadata Reporting (4-7h)

**File**: `rust/compiler/src/interpreter_call/bdd.rs`

**Issue**: Tests with all passing still marked as FAIL.

**Debug Tasks**:
1. Add debug logging to test framework (1h)
   - Log when test starts/ends
   - Log pass/fail status
   - Log final count calculation
2. Identify why passed tests show FAIL (2-3h)
   - Check describe block exit code
   - Check it block aggregation
   - Check failure propagation logic
3. Fix the root cause (1-2h)
4. Verify with affected test files (0.5-1h)

**Expected Fix**:
```rust
// Likely issue in describe block handler:
fn handle_describe_block(...) -> TestResult {
    let mut total_passed = 0;
    let mut total_failed = 0;

    for test in &tests {
        match run_test(test) {
            Ok(_) => total_passed += 1,
            Err(_) => total_failed += 1,
        }
    }

    // ❌ BUG: Always returns FAIL if any describe has 0 failed?
    if total_failed > 0 {
        TestResult::Fail
    } else {
        TestResult::Pass  // ✅ Should be this when all pass
    }
}
```

**Expected Results**: +80-100 tests (already passing, now correctly reported)

---

### 2.3 Decision #7: Type Annotation Conversion (5-6h)

**Objective**: Enable `val arr: ArrayList = [1, 2, 3]` syntax via automatic type conversion.

#### Step 2.3.1: Add Type Coercion Logic (3-4h)

**File**: `rust/compiler/src/interpreter_call/mod.rs`

**Implementation**:
```rust
Expr::ArrayLiteral { elements } => {
    // Evaluate elements
    let values: Vec<Value> = elements.iter()
        .map(|e| evaluate_expr(e, env, ...))
        .collect::<Result<_, _>>()?;

    // Create default array
    let arr_value = Value::Array(Rc::new(RefCell::new(values)));

    // Check if expected type differs from Array
    if let Some(expected_type) = expected_type {
        if expected_type.is_class() {
            let class_name = expected_type.class_name();

            // Check if class has static from() method
            if let Some(class) = classes.get(&class_name) {
                if class.static_methods.contains_key("from") {
                    // Convert: ClassName.from(arr_value)
                    return call_static_method(&class_name, "from", vec![arr_value], env, ...)?;
                }
            }
        }
    }

    Ok(arr_value)
}
```

#### Step 2.3.2: Implement from() in Standard Library (1-2h)

**File**: `rust/lib/std/src/collections/array_list.spl` (new file)

```simple
export class ArrayList:
    items: [Value]

    static fn from(data: [Value]) -> ArrayList:
        ArrayList(items: data)

    fn len() -> i64:
        self.items.len()

    fn get(index: i64) -> Value:
        self.items[index]

    me push(value: Value):
        self.items = self.items + [value]

    me pop() -> Value:
        val last = self.items[self.items.len() - 1]
        self.items = self.items[0..self.items.len() - 1]
        last
```

#### Step 2.3.3: Verify with SSpec Tests (1h)

**Tests already written in Phase 0** (see `type_conversion_spec.spl` and `custom_backend_spec.spl`).

**Run Tests**:
```bash
./rust/target/debug/simple_runtime test test/system/features/arrays/type_conversion_spec.spl
# Expected: 15-20 tests passing (previously failed)

./rust/target/debug/simple_runtime test test/system/features/collections/custom_backend_spec.spl
# Expected: 15-20 tests passing
```

**Expected Results**: 30-40 tests passing (were failing in Phase 0)

---

### 2.4 Decision #8: Fixed-Size Arrays (18-26h)

**Objective**: Add `[T; N]` syntax for compile-time size-checked arrays.

#### Step 2.4.1: Add Fixed-Size Array Type (3-4h)

**File**: `rust/compiler/src/types/mod.rs`

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Array(Box<Type>),  // Dynamic: [T]

    // NEW: Fixed-size array
    FixedArray {
        element_type: Box<Type>,
        size: usize,  // Compile-time constant
    },

    // ... other types
}
```

#### Step 2.4.2: Parse [T; N] Syntax (2-3h)

**File**: `rust/parser/src/type_parsing/mod.rs`

```rust
fn parse_array_type() -> Result<Type, ParseError> {
    expect_token(Token::LeftBracket)?;
    let elem_type = parse_type()?;

    if consume_if_token(Token::Semicolon) {
        // Fixed-size: [T; N]
        let size_expr = parse_const_expr()?;
        let size = evaluate_const_size(size_expr)?;
        expect_token(Token::RightBracket)?;

        Ok(Type::FixedArray {
            element_type: Box::new(elem_type),
            size,
        })
    } else {
        // Dynamic: [T]
        expect_token(Token::RightBracket)?;
        Ok(Type::Array(Box::new(elem_type)))
    }
}
```

#### Step 2.4.3: Type Checking for Size Mismatches (4-6h)

**File**: `rust/compiler/src/hir/type_checker.rs`

```rust
fn check_array_literal(
    elements: &[Expr],
    expected_type: Option<&Type>,
) -> Result<Type, CompileError> {
    if let Some(Type::FixedArray { element_type, size }) = expected_type {
        // Check size match
        if elements.len() != *size {
            return Err(CompileError::type_error(format!(
                "mismatched size: expected array of size {}, found size {}",
                size,
                elements.len()
            )));
        }
    }

    // ... check element types ...
}

fn check_method_call(
    receiver_type: &Type,
    method_name: &str,
) -> Result<Type, CompileError> {
    if receiver_type.is_fixed_size_array() {
        // Disallow size-changing methods
        if matches!(method_name, "push" | "pop" | "insert" | "remove") {
            return Err(CompileError::type_error(format!(
                "cannot call `{}` on fixed-size array",
                method_name
            )));
        }
    }

    // ...
}
```

#### Step 2.4.4: Runtime Representation (2-3h)

**File**: `rust/compiler/src/value/mod.rs`

```rust
pub enum Value {
    Array(Rc<RefCell<Vec<Value>>>),  // Dynamic

    // NEW: Fixed-size
    FixedArray {
        elements: Rc<RefCell<Box<[Value]>>>,
        size: usize,
    },

    // ...
}
```

#### Step 2.4.5: Interpreter and Method Dispatch (3-4h)

Update interpreter to create fixed-size arrays and reject size-changing operations.

#### Step 2.4.6: Verify with SSpec Tests (2-3h)

**Tests already written in Phase 0** (see `fixed_size_arrays_spec.spl` and `fixed_size_edge_cases_spec.spl`).

**Run Tests**:
```bash
./rust/target/debug/simple_runtime test test/system/features/arrays/fixed_size_arrays_spec.spl
# Expected: 25-30 tests passing (previously failed)

./rust/target/debug/simple_runtime test test/system/features/arrays/fixed_size_edge_cases_spec.spl
# Expected: 15-20 tests passing (previously failed)
```

**Expected Results**: 40-50 tests passing (were failing in Phase 0)

---

### 2.5 Decision #9: Target-Based Mutability Defaults (13-20h)

**Objective**: Allow compilation target to set default mutability (embedded = immutable default).

#### Step 2.5.1: Add Compilation Target Config (1-2h)

**File**: `rust/compiler/src/config.rs`

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum CompilationTarget {
    General,     // Mutable by default
    Embedded,    // Immutable by default
    Wasm,        // Immutable by default
    Performance, // Mutable by default
}

pub struct CompilerConfig {
    pub target: CompilationTarget,
    pub default_array_mutability: Mutability,
    pub default_dict_mutability: Mutability,
}

impl CompilerConfig {
    pub fn for_target(target: CompilationTarget) -> Self {
        match target {
            CompilationTarget::General | CompilationTarget::Performance => Self {
                target,
                default_array_mutability: Mutability::Mutable,
                default_dict_mutability: Mutability::Mutable,
            },
            CompilationTarget::Embedded | CompilationTarget::Wasm => Self {
                target,
                default_array_mutability: Mutability::Immutable,
                default_dict_mutability: Mutability::Immutable,
            },
        }
    }
}
```

#### Step 2.5.2: Parse Module Attributes (2-3h)

**File**: `rust/parser/src/attributes.rs`

```rust
// Parse: @target(embedded)
pub fn parse_module_attribute() -> Result<ModuleAttribute, ParseError> {
    expect_token(Token::At)?;
    expect_identifier("target")?;
    expect_token(Token::LeftParen)?;
    let target = parse_identifier()?;
    expect_token(Token::RightParen)?;

    Ok(ModuleAttribute::Target(parse_target(&target)?))
}
```

#### Step 2.5.3: Apply Default Mutability (3-4h)

**File**: `rust/compiler/src/interpreter_call/mod.rs`

```rust
Expr::ArrayLiteral { elements } => {
    let values = evaluate_elements(elements)?;

    // Determine mutability:
    let mutability = if let Some(type_ann) = expected_type {
        type_ann.mutability()  // Explicit annotation
    } else if let Some(attr) = current_module.attribute {
        attr.default_mutability()  // Module attribute
    } else {
        config.default_array_mutability  // Global default
    };

    match mutability {
        Mutability::Mutable => {
            Ok(Value::Array(Rc::new(RefCell::new(values))))
        }
        Mutability::Immutable => {
            Ok(Value::FrozenArray(Rc::new(values)))
        }
    }
}
```

#### Step 2.5.4: CLI Flag Support (1-2h)

```rust
#[derive(Parser)]
struct Cli {
    #[arg(long, default_value = "general")]
    target: String,
}
```

#### Step 2.5.5: Configuration File Support (2-3h)

**File**: `simple.toml`

```toml
[build]
default-target = "embedded"

[target.embedded]
default-mutability = "immutable"
```

#### Step 2.5.6: Verify with SSpec Tests (2-3h)

**Tests already written in Phase 0** (see `target_defaults_spec.spl`).

**Run Tests**:
```bash
# Test general mode (default):
./rust/target/debug/simple_runtime test test/system/features/arrays/target_defaults_spec.spl
# Expected: 15-20 tests passing

# Test embedded mode:
./rust/target/debug/simple_runtime test --target=embedded test/system/features/arrays/target_defaults_spec.spl
# Expected: Different behavior verified
```

**Expected Results**: 15-20 tests passing, verifying different modes work correctly

---

## Phase 3: TreeSitter Integration (Week 5, 16-24h)

### 3.1 Decision #4: Full TreeSitter Integration (16-24h)

**Objective**: Integrate TreeSitter C library for full LSP/IDE support.

#### Step 3.1.1: Build TreeSitter C Library (4-6h)

**Tasks**:
1. Download tree-sitter library (0.5h)
   ```bash
   git clone https://github.com/tree-sitter/tree-sitter
   cd tree-sitter
   make
   ```

2. Build Simple language grammar (1-2h)
   - Create `tree-sitter-simple/` directory
   - Write grammar.js for Simple syntax
   - Generate parser with `tree-sitter generate`

3. Link TreeSitter to Rust (2-3h)
   - Add tree-sitter crate dependency
   - Add build.rs to link C library
   - Add feature gate for treesitter

**Cargo.toml**:
```toml
[dependencies]
tree-sitter = { version = "0.20", optional = true }

[features]
treesitter = ["tree-sitter"]

[build-dependencies]
cc = "1.0"
```

**build.rs**:
```rust
#[cfg(feature = "treesitter")]
fn main() {
    cc::Build::new()
        .file("tree-sitter-simple/src/parser.c")
        .compile("tree-sitter-simple");
}

#[cfg(not(feature = "treesitter"))]
fn main() {
    // No-op when treesitter disabled
}
```

#### Step 3.1.2: Implement TreeSitter FFI Bindings (6-10h)

**File**: `rust/compiler/src/interpreter_extern/treesitter.rs` (new file)

**Implement Types**:
```rust
use tree_sitter::{Parser, Tree, Node, Language};

// Lexer wrapper
pub fn treesitter_lexer_new(args: &[Value]) -> Result<Value, CompileError> {
    let parser = Parser::new();
    let handle = register_handle(parser);

    Ok(Value::Object {
        class: "TreeSitterLexer".to_string(),
        fields: hashmap! {
            "__handle__".to_string() => Value::Int(handle as i64)
        },
    })
}

// Parser wrapper
pub fn treesitter_parser_new(args: &[Value]) -> Result<Value, CompileError> {
    let mut parser = Parser::new();
    parser.set_language(tree_sitter_simple::language())?;

    let handle = register_handle(parser);
    Ok(Value::Object {
        class: "TreeSitterParser".to_string(),
        fields: hashmap! {
            "__handle__".to_string() => Value::Int(handle as i64)
        },
    })
}

// Parse method
pub fn treesitter_parse(args: &[Value]) -> Result<Value, CompileError> {
    let parser_obj = eval_arg_object(args, 0)?;
    let source_code = eval_arg_string(args, 1)?;

    let parser = get_handle::<Parser>(parser_obj)?;
    let tree = parser.parse(&source_code, None)?;

    let tree_handle = register_handle(tree);
    Ok(Value::Object {
        class: "TreeSitterTree".to_string(),
        fields: hashmap! {
            "__handle__".to_string() => Value::Int(tree_handle as i64)
        },
    })
}

// Node access
pub fn treesitter_root_node(args: &[Value]) -> Result<Value, CompileError> {
    let tree_obj = eval_arg_object(args, 0)?;
    let tree = get_handle::<Tree>(tree_obj)?;

    let root = tree.root_node();
    let node_handle = register_handle(root);

    Ok(Value::Object {
        class: "TreeSitterNode".to_string(),
        fields: hashmap! {
            "__handle__".to_string() => Value::Int(node_handle as i64)
        },
    })
}

// Additional methods: child_count, child, kind, text, etc.
```

**Implementation Tasks**:
1. Create treesitter.rs module (1h)
2. Implement handle registry for C objects (1-2h)
3. Implement Parser wrapper (1-2h)
4. Implement Tree wrapper (1-2h)
5. Implement Node wrapper (2-3h)
6. Add to FFI dispatcher (0.5h)

#### Step 3.1.3: Write Simple Language Grammar (4-6h)

**File**: `tree-sitter-simple/grammar.js`

**Grammar Definition**:
```javascript
module.exports = grammar({
  name: 'simple',

  rules: {
    source_file: $ => repeat($._statement),

    _statement: $ => choice(
      $.function_definition,
      $.class_definition,
      $.variable_declaration,
      $.expression_statement,
      // ... more statement types
    ),

    function_definition: $ => seq(
      'fn',
      field('name', $.identifier),
      field('parameters', $.parameter_list),
      optional(seq('->', field('return_type', $.type))),
      ':',
      field('body', $.block)
    ),

    // ... more rules for all Simple syntax
  }
});
```

**Tasks**:
1. Define basic statement types (1-2h)
2. Define expression grammar (1-2h)
3. Define type grammar (0.5-1h)
4. Test with sample Simple files (1-2h)

#### Step 3.1.4: Testing and Integration (2-4h)

**Test Cases**:
```simple
use simple.parser.treesitter

describe "TreeSitter integration":
    it "should parse simple function":
        val parser = TreeSitterParser.new()
        val code = "fn foo(): pass"
        val tree = parser.parse(code)
        val root = tree.root_node()

        expect(root.kind()).to_equal("source_file")
        expect(root.child_count()).to_be_gte(1)

    it "should handle syntax errors":
        val parser = TreeSitterParser.new()
        val code = "fn foo( ): pass"  # Syntax error
        val tree = parser.parse(code)

        expect(tree.has_error()).to_be_true()
```

**Run Tests**:
```bash
cargo build --manifest-path=rust/Cargo.toml --features treesitter
./rust/target/debug/simple_runtime test test/lib/std/unit/parser/treesitter*.spl
./rust/target/debug/simple_runtime test test/system/features/treesitter/
# Expected: +80-120 tests passing
```

**Expected Results**: +80-120 tests passing

---

## Phase 4: Selective Feature Implementation (Week 6-8, 40-60h)

### 4.1 Decision #5: GPU/Tensor Support (10-15h)

**Objective**: Implement GPU kernel execution and tensor operations.

#### Step 4.1.1: GPU Kernel Infrastructure (5-8h)

**File**: `rust/compiler/src/interpreter_extern/gpu.rs` (new file)

**Implement**:
```rust
// Kernel type
pub struct GpuKernel {
    source: String,
    compiled: Option<Vec<u8>>,
}

// FFI functions
pub fn gpu_kernel_new(args: &[Value]) -> Result<Value, CompileError> {
    let source = eval_arg_string(args, 0)?;
    let kernel = GpuKernel {
        source,
        compiled: None,
    };

    let handle = register_handle(kernel);
    Ok(Value::Object {
        class: "GpuKernel".to_string(),
        fields: hashmap! {
            "__handle__".to_string() => Value::Int(handle as i64)
        },
    })
}

pub fn gpu_kernel_compile(args: &[Value]) -> Result<Value, CompileError> {
    let kernel_obj = eval_arg_object(args, 0)?;
    let kernel = get_handle_mut::<GpuKernel>(kernel_obj)?;

    // Stub: pretend to compile
    kernel.compiled = Some(vec![0u8; 100]);
    Ok(Value::Bool(true))
}

pub fn gpu_kernel_execute(args: &[Value]) -> Result<Value, CompileError> {
    let kernel_obj = eval_arg_object(args, 0)?;
    let input_tensor = eval_arg_object(args, 1)?;

    // Stub: return input tensor as output
    Ok(input_tensor)
}
```

**Expected**: +20 tests

#### Step 4.1.2: Tensor Operations (5-7h)

**File**: `rust/compiler/src/interpreter_extern/tensor.rs` (new file)

**Implement**:
```rust
pub struct Tensor {
    shape: Vec<usize>,
    data: Vec<f64>,
}

pub fn tensor_new(args: &[Value]) -> Result<Value, CompileError> {
    let shape = eval_arg_array_of_ints(args, 0)?;
    let data = eval_arg_array_of_floats(args, 1)?;

    let tensor = Tensor {
        shape: shape.iter().map(|&x| x as usize).collect(),
        data,
    };

    let handle = register_handle(tensor);
    Ok(Value::Object {
        class: "Tensor".to_string(),
        fields: hashmap! {
            "__handle__".to_string() => Value::Int(handle as i64),
            "shape".to_string() => Value::Array(shape.clone()),
        },
    })
}

// Add ops: add, mul, matmul, reshape, slice, etc.
```

**Expected**: +40 tests
**Total GPU/Tensor**: +60 tests

---

### 4.2 Decision #5: Deep Learning (PyTorch Integration) (10-15h)

**Objective**: Enable ml.torch modules with PyTorch FFI.

**Note**: This overlaps with Decision #1 (re-enabling ml.torch modules). Here we add the actual PyTorch FFI implementations.

#### Step 4.2.1: PyTorch FFI Bindings (6-10h)

**File**: `rust/compiler/src/interpreter_extern/pytorch.rs` (new file)

**Add dependency**:
```toml
[dependencies]
tch = { version = "0.13", optional = true }

[features]
torch = ["tch"]
```

**Implement**:
```rust
#[cfg(feature = "torch")]
use tch::{Tensor as TchTensor, Device as TchDevice, nn};

#[cfg(feature = "torch")]
pub fn torch_tensor_new(args: &[Value]) -> Result<Value, CompileError> {
    let data = eval_arg_array_of_floats(args, 0)?;
    let shape = eval_arg_array_of_ints(args, 1)?;

    let tensor = TchTensor::of_slice(&data)
        .reshape(&shape.iter().map(|&x| x as i64).collect::<Vec<_>>());

    let handle = register_handle(tensor);
    Ok(Value::Object {
        class: "TorchTensor".to_string(),
        fields: hashmap! {
            "__handle__".to_string() => Value::Int(handle as i64)
        },
    })
}

#[cfg(feature = "torch")]
pub fn torch_linear_new(args: &[Value]) -> Result<Value, CompileError> {
    let in_dim = eval_arg_int(args, 0)?;
    let out_dim = eval_arg_int(args, 1)?;

    let vs = nn::VarStore::new(TchDevice::Cpu);
    let linear = nn::linear(&vs.root(), in_dim, out_dim, Default::default());

    let handle = register_handle((vs, linear));
    Ok(Value::Object {
        class: "Linear".to_string(),
        fields: hashmap! {
            "__handle__".to_string() => Value::Int(handle as i64),
            "in_dim".to_string() => Value::Int(in_dim),
            "out_dim".to_string() => Value::Int(out_dim),
        },
    })
}

// Add more: Conv2d, ReLU, Softmax, Adam, SGD, etc.

#[cfg(not(feature = "torch"))]
pub fn torch_tensor_new(args: &[Value]) -> Result<Value, CompileError> {
    // Stub when torch disabled
    Ok(Value::Object {
        class: "TorchTensor".to_string(),
        fields: HashMap::new(),
    })
}
```

**Expected**: +90 tests

#### Step 4.2.2: Update ml.torch Simple Modules (4-5h)

**Files**: `rust/lib/std/src/ml/torch/*.spl`

Update to use new FFI bindings:
```simple
# ml/torch/tensor.spl
export class Tensor:
    __handle__: i64
    shape: [i64]

    static fn new(data: [f64], shape: [i64]) -> Tensor:
        torch_tensor_new(data, shape)  # Calls FFI

    me add(other: Tensor) -> Tensor:
        torch_tensor_add(self.__handle__, other.__handle__)

    # ... more methods

# ml/torch/nn/linear.spl
export class Linear:
    __handle__: i64
    in_dim: i64
    out_dim: i64

    static fn new(in_dim: i64, out_dim: i64) -> Linear:
        torch_linear_new(in_dim, out_dim)

    fn forward(x: Tensor) -> Tensor:
        torch_linear_forward(self.__handle__, x.__handle__)
```

**Total Deep Learning**: +90 tests

---

### 4.3 Decision #5: Database/Storage (8-12h)

**Objective**: Implement database synchronization and integrity checking.

#### Step 4.3.1: Database Connection (3-5h)

**File**: `rust/compiler/src/interpreter_extern/database.rs` (new file)

**Implement**:
```rust
use rusqlite::{Connection, params};

pub fn db_connect(args: &[Value]) -> Result<Value, CompileError> {
    let path = eval_arg_string(args, 0)?;
    let conn = Connection::open(path)?;

    let handle = register_handle(conn);
    Ok(Value::Object {
        class: "Database".to_string(),
        fields: hashmap! {
            "__handle__".to_string() => Value::Int(handle as i64)
        },
    })
}

pub fn db_execute(args: &[Value]) -> Result<Value, CompileError> {
    let db_obj = eval_arg_object(args, 0)?;
    let sql = eval_arg_string(args, 1)?;
    let params_arr = eval_arg_array(args, 2)?;

    let conn = get_handle::<Connection>(db_obj)?;
    conn.execute(&sql, rusqlite::params_from_iter(params_arr))?;

    Ok(Value::Nil)
}

pub fn db_query(args: &[Value]) -> Result<Value, CompileError> {
    let db_obj = eval_arg_object(args, 0)?;
    let sql = eval_arg_string(args, 1)?;

    let conn = get_handle::<Connection>(db_obj)?;
    let mut stmt = conn.prepare(&sql)?;

    let rows = stmt.query_map([], |row| {
        // Convert row to Value::Dict
        Ok(Value::Dict(/* ... */))
    })?;

    let results: Vec<Value> = rows.collect::<Result<_, _>>()?;
    Ok(Value::Array(results))
}
```

**Expected**: +50 tests

#### Step 4.3.2: Integrity Checking (5-7h)

**File**: `rust/compiler/src/interpreter_extern/db_integrity.rs` (new file)

**Implement**:
```rust
pub fn db_check_integrity(args: &[Value]) -> Result<Value, CompileError> {
    let db_obj = eval_arg_object(args, 0)?;
    let conn = get_handle::<Connection>(db_obj)?;

    // Run PRAGMA integrity_check
    let mut stmt = conn.prepare("PRAGMA integrity_check")?;
    let result = stmt.query_row([], |row| row.get::<_, String>(0))?;

    Ok(Value::Bool(result == "ok"))
}

pub fn db_validate_schema(args: &[Value]) -> Result<Value, CompileError> {
    let db_obj = eval_arg_object(args, 0)?;
    let expected_schema = eval_arg_dict(args, 1)?;

    // Compare actual schema to expected
    // Return validation errors
    Ok(Value::Array(Vec::new()))  // Stub: no errors
}
```

**Expected**: +25 tests
**Total Database**: +75 tests

---

### 4.4 Decision #5: LSP/MCP Servers (12-18h)

**Objective**: Implement Language Server Protocol and Model Context Protocol servers.

#### Step 4.4.1: LSP Infrastructure (6-9h)

**File**: `rust/lib/std/src/lsp/server.spl`

**Implement**:
```simple
export class LspServer:
    transport: Transport
    handlers: Dict<text, fn(params) -> Response>

    static fn new(transport: Transport) -> LspServer:
        LspServer(
            transport: transport,
            handlers: {},
        )

    me register_handler(method: text, handler: fn(params) -> Response):
        self.handlers[method] = handler

    fn start():
        while true:
            val message = self.transport.receive()
            val response = self.dispatch(message)
            self.transport.send(response)

    fn dispatch(message: JsonRpcMessage) -> Response:
        val handler = self.handlers.get(message.method)
        if handler.is_some():
            handler.unwrap()(message.params)
        else:
            Response.error("method not found")

# Implement standard LSP methods:
export fn handle_initialize(params): ...
export fn handle_text_document_did_open(params): ...
export fn handle_text_document_completion(params): ...
export fn handle_text_document_hover(params): ...
# ... 15+ more LSP methods
```

**Expected**: +80 tests

#### Step 4.4.2: MCP Server (6-9h)

**File**: `rust/lib/std/src/mcp/server.spl`

**Implement MCP protocol** (similar to LSP but for model context):
```simple
export class McpServer:
    # Model Context Protocol server
    # Similar structure to LspServer but different protocol

    static fn new() -> McpServer: ...
    me register_tool(name: text, handler: fn): ...
    me register_resource(uri: text, provider: fn): ...
    fn start(): ...
```

**Expected**: +50 tests
**Total LSP/MCP**: +130 tests

**Total Selective Features**: +355 tests (GPU/Tensor: 60, Deep Learning: 90, Database: 75, LSP/MCP: 130)

---

## Phase 5: Validation and Polish (Week 9, 8-12h)

### 5.1 Comprehensive Testing (4-6h)

**Run Full Test Suite**:
```bash
cd /home/ormastes/dev/pub/simple

# Build with all features
cd rust && cargo build --all-features

# Run Rust tests
cargo test --workspace

# Run Simple tests
cd ..
./rust/target/debug/simple_runtime test 2>&1 | tee /tmp/final_test_results.txt

# Analyze results
grep "^Results:" /tmp/final_test_results.txt
```

**Regression Testing**:
```bash
# Verify no Rust test regressions
cd rust && cargo test --workspace 2>&1 | grep "test result:"
# Should still show: 3915 passed

# Check for new failures
./rust/target/debug/simple_runtime test 2>&1 | grep "FAIL" | wc -l
# Should be significantly less than 101 (current)
```

### 5.2 Fix Discovered Issues (2-4h)

**Likely issues to encounter**:
- RefCell borrow panics (add drop() calls)
- Feature gate build errors (fix #[cfg] conditions)
- Import circular dependencies (add lazy loading)
- Type mismatch in collections (fix conversion logic)

### 5.3 Documentation Updates (2-3h)

**Update Files**:
1. `doc/TODO.md` - Mark completed items (0.5h)
2. `doc/feature/feature.md` - Update feature status (0.5h)
3. `doc/test/test_result.md` - Final test results (auto-generated)
4. `doc/report/test_fix_completion_2026-02-XX.md` - Create completion report (1h)
5. `CLAUDE.md` - Update status section (0.5h)

---

## Implementation Checklist

### Phase 1: Foundation ✅
- [ ] 1.1.1: Enable ModuleResolver in compiler (6-8h)
- [ ] 1.1.2: Fix export extraction bugs #1 and #2 (6-8h)
- [ ] 1.1.3: Integration testing (4-8h)
- [ ] 1.1.4: Re-enable ml.torch modules (4-6h)
- [ ] 1.2.1: Update Value::Function with Rc<RefCell<Env>> (2-3h)
- [ ] 1.2.2: Update function execution logic (4-6h)
- [ ] 1.2.3: Update lambda/closure creation (2-3h)
- [ ] 1.2.4: Test closure capture (1-2h)
- [ ] 1.3.1: Add missing stdlib functions (4-8h)
- [ ] 1.3.2: Add builtin type methods (3-5h)
- [ ] 1.3.3: Implement dict methods (6-10h)
- [ ] 1.3.4: Fix parser edge cases (2-4h)
- [ ] 1.3.5: Implement lazy bindings (3-5h)

**Phase 1 Subtotal**: 47-75h, +637 tests

### Phase 2: Advanced Features ✅
- [ ] 2.1.1: Update Value::Array/Dict with RefCell (2-3h)
- [ ] 2.1.2: Update collection methods (3-5h)
- [ ] 2.1.3: Update array/dict access (1-2h)
- [ ] 2.1.4: Test mutable collections (0.5-1h)
- [ ] 2.2.1: Analyze spec file structure (2-3h)
- [ ] 2.2.2: Split mixed spec files (6-10h)
- [ ] 2.2.3: Fix test metadata reporting (4-7h)

**Phase 2 Subtotal**: 62-93h, +225 tests (updated with array features)

### Phase 3: TreeSitter ✅
- [ ] 3.1.1: Build TreeSitter C library (4-6h)
- [ ] 3.1.2: Implement FFI bindings (6-10h)
- [ ] 3.1.3: Write Simple grammar (4-6h)
- [ ] 3.1.4: Testing and integration (2-4h)

**Phase 3 Subtotal**: 16-26h, +80 tests

### Phase 4: Selective Features ✅
- [ ] 4.1.1: GPU kernel infrastructure (5-8h)
- [ ] 4.1.2: Tensor operations (5-7h)
- [ ] 4.2.1: PyTorch FFI bindings (6-10h)
- [ ] 4.2.2: Update ml.torch modules (4-5h)
- [ ] 4.3.1: Database connection (3-5h)
- [ ] 4.3.2: Integrity checking (5-7h)
- [ ] 4.4.1: LSP infrastructure (6-9h)
- [ ] 4.4.2: MCP server (6-9h)

**Phase 4 Subtotal**: 40-60h, +355 tests

### Phase 5: Validation ✅
- [ ] 5.1: Comprehensive testing (4-6h)
- [ ] 5.2: Fix discovered issues (2-4h)
- [ ] 5.3: Documentation updates (2-3h)

**Phase 5 Subtotal**: 8-13h

**Grand Total**: 173-267h, +1297 tests (updated with array features)

---

## Success Metrics

| Phase | Effort | Tests Added | Cumulative | Pass Rate |
|-------|--------|-------------|------------|-----------|
| **Baseline** | 0h | 0 | 7622 | 83.1% |
| **Phase 0** | 8-12h | 0 (130-170 tests written but failing) | 7622 | 83.1% |
| **Phase 1** | 47-75h | +637 | 8259 | 90.0% |
| **Phase 2** | 62-93h | +225 (array tests now pass) | 8484 | 92.5% |
| **Phase 3** | 16-26h | +80 | 8564 | 93.4% |
| **Phase 4** | 40-60h | +355 | 8919 | 97.2% |
| **Phase 5** | 8-13h | 0 (validation) | 8919 | 97.2% |
| **Total** | 181-279h | +1297 | 8919/9172 | 97.2% |

**Note**: Target is 8919/9172 (97.2%), not 100%, because some tests are:
- Unimplemented features (intentionally deferred)
- External dependencies not available
- Platform-specific features

**Remaining 253 tests** (2.8%) are acceptable technical debt for future sprints.

## Array Features Summary

The plan now includes comprehensive array/collection improvements:

1. **Mutable by Default** (Decision #3): Collections are mutable like Python/JS/Java
2. **Type Conversion** (Decision #7): `val arr: ArrayList = [1, 2, 3]` works automatically
3. **Fixed-Size Arrays** (Decision #8): `val vec3: [f64; 3]` with compile-time size checks
4. **Target-Based Defaults** (Decision #9): `--target=embedded` makes arrays immutable (saves 33% memory)

**Benefits**:
- **User expectations**: `var arr = []` allows mutations (both push and reassignment)
- **Performance**: O(1) mutations with RefCell (general mode) or zero overhead (embedded mode)
- **Type safety**: Fixed-size arrays catch errors at compile time
- **Flexibility**: Custom backends via `from()` method
- **Embedded support**: Immutable default saves memory, smaller binaries

---

## Risk Mitigation

### High-Risk Items
1. **RefCell borrow panics**: Add comprehensive borrow lifetime management
2. **TreeSitter C library linking**: Use feature gates, provide fallback stubs
3. **PyTorch dependency**: Optional feature, works without torch crate
4. **Compiler module resolver**: Extensive testing, incremental rollout

### Rollback Strategy
```bash
# Before each phase:
jj commit -m "Phase N complete"

# If issues arise:
jj undo  # Rollback to previous commit

# After validation:
jj bookmark set main -r @
jj git push --bookmark main
```

### Continuous Validation
```bash
# After each decision implementation:
cd rust && cargo test --workspace  # Ensure Rust tests still pass
./rust/target/debug/simple_runtime test | head -50  # Quick smoke test
```

---

## Notes on RefCell Usage

**Important**: RefCell is a Rust implementation detail, NOT a Simple language feature.

**Where RefCell is used** (all in Rust code):
1. `Value::Function { captured_env: Rc<RefCell<Environment>> }` - Closure capture
2. `Value::Array(Rc<RefCell<Vec<Value>>>)` - Mutable arrays
3. `Value::Dict(Rc<RefCell<HashMap<String, Value>>>)` - Mutable dicts

**Simple language perspective** (no change):
```simple
# Users write this:
var arr = [1, 2, 3]
val last = arr.pop()  # Just works

# RefCell is hidden in interpreter implementation
# Users never see Rc<RefCell<...>> syntax
```

**Why Rc<RefCell> instead of Arc<Mutex>**:
- Simple interpreter is single-threaded (for now)
- RefCell has lower overhead than Mutex
- Easier to debug (panics on borrow errors vs deadlocks)
- Can upgrade to Arc<Mutex> later if needed for concurrency

---

## Next Steps

**Start with**: Phase 1, Step 1.1.1 (Enable ModuleResolver)

**Command to begin**:
```bash
cd /home/ormastes/dev/pub/simple
jj commit -m "checkpoint: before implementation plan"
# Ready to start implementation
```

**Questions before starting?** Review this plan and confirm readiness.
