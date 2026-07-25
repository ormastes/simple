# Fixed-Size Arrays with Compile-Time Size Checking

**Date**: 2026-01-31
**Question**: "can set primitive size fixed array? size change cause compile error. type inference to check it compile time possible and runtime if not possible."

---

## The Goal

**Fixed-size arrays** where size is part of the type:

```simple
val vec3: [f64; 3] = [1.0, 2.0, 3.0]  # OK: exactly 3 elements
val vec3: [f64; 3] = [1.0, 2.0]        # ERROR: size mismatch (compile-time)

vec3.push(4.0)  # ERROR: cannot change size of fixed array (compile-time)
vec3[0] = 5.0   # OK: mutation doesn't change size
```

**Benefits**:
- Catch size errors at compile time
- Better performance (no bounds checking, stack allocation)
- Clear intent (this is a 3D vector, not a generic array)
- Type safety (can't accidentally mix vec3 and vec4)

---

## Design: Three-Level Type System

### Level 1: Dynamic Arrays `[T]`

**Mutable size** (existing):

```simple
var arr: [i64] = [1, 2, 3]  # Dynamic array
arr.push(4)     # OK: size can change
arr.pop()       # OK: size can change
arr[0] = 10     # OK: mutation
```

**Backend**: `Rc<RefCell<Vec<Value>>>`
**Size**: Runtime, can change

### Level 2: Fixed-Size Arrays `[T; N]`

**Immutable size** (new):

```simple
val vec3: [f64; 3] = [1.0, 2.0, 3.0]  # Fixed-size array
vec3.push(4.0)  # ERROR: cannot push to fixed-size array
vec3.pop()      # ERROR: cannot pop from fixed-size array
vec3[0] = 10.0  # OK: mutation doesn't change size
```

**Backend**: `Rc<RefCell<[Value; N]>>` (Rust fixed array)
**Size**: Compile-time constant, cannot change

### Level 3: Const Arrays `const [T; N]`

**Immutable size + immutable data** (new):

```simple
val UNIT_X: const [f64; 3] = [1.0, 0.0, 0.0]
UNIT_X[0] = 2.0  # ERROR: cannot mutate const array
UNIT_X.push(1.0) # ERROR: cannot change size
```

**Backend**: `Rc<[Value; N]>` (no RefCell)
**Size**: Compile-time constant, cannot change

---

## Syntax

### Type Annotations

```simple
# Dynamic array (size can change):
val arr: [i64] = [1, 2, 3]

# Fixed-size array (size cannot change):
val vec3: [f64; 3] = [1.0, 2.0, 3.0]

# Const fixed-size array (size and data immutable):
val ORIGIN: const [f64; 3] = [0.0, 0.0, 0.0]
```

### Type Inference

```simple
# Infer dynamic array:
val arr = [1, 2, 3]  # Type: [i64] (dynamic)

# Infer fixed-size array (when used with fixed-size function):
fn dot(a: [f64; 3], b: [f64; 3]) -> f64:
    a[0] * b[0] + a[1] * b[1] + a[2] * b[2]

val v1 = [1.0, 2.0, 3.0]  # Type: [f64] (dynamic by default)
val v2: [f64; 3] = [1.0, 2.0, 3.0]  # Type: [f64; 3] (explicit)

dot(v1, v2)  # ERROR: v1 is dynamic, not fixed-size
dot(v2, v2)  # OK: both fixed-size
```

### Literal Syntax

**Option A: Explicit type annotation** (recommended):
```simple
val vec3: [f64; 3] = [1.0, 2.0, 3.0]  # Fixed-size via annotation
```

**Option B: Suffix syntax** (alternative):
```simple
val vec3 = [1.0, 2.0, 3.0]#3  # Fixed-size via suffix (ugly)
```

**Option C: Array constructor**:
```simple
val vec3 = array![f64; 3](1.0, 2.0, 3.0)  # Macro-like syntax
```

**Recommendation**: Use **Option A** (type annotation) - clearest and most explicit.

---

## Compile-Time Size Checking

### Rule 1: Size Mismatch (Literal)

```simple
val vec3: [f64; 3] = [1.0, 2.0]  # ERROR at compile time
```

**Error message**:
```
error[E0308]: mismatched size
 --> test.spl:1:22
  |
1 | val vec3: [f64; 3] = [1.0, 2.0]
  |           --------   ^^^^^^^^^^^ expected array of size 3, found size 2
  |           |
  |           expected due to this type annotation
  |
help: add missing element
  |
1 | val vec3: [f64; 3] = [1.0, 2.0, 0.0]
  |                                  +++
```

### Rule 2: Size-Changing Operations

```simple
val vec3: [f64; 3] = [1.0, 2.0, 3.0]
vec3.push(4.0)  # ERROR at compile time
```

**Error message**:
```
error[E0599]: no method named `push` found for fixed-size array `[f64; 3]`
 --> test.spl:2:6
  |
2 | vec3.push(4.0)
  |      ^^^^ method not found in `[f64; 3]`
  |
  = note: `push` is only available for dynamic arrays `[T]`
  = help: convert to dynamic array first: `vec3.to_dynamic().push(4.0)`
  = help: or use indexing to replace an element: `vec3[2] = 4.0`
```

### Rule 3: Function Parameter Size Mismatch

```simple
fn process(v: [f64; 3]):
    # ...

val vec4: [f64; 4] = [1.0, 2.0, 3.0, 4.0]
process(vec4)  # ERROR at compile time
```

**Error message**:
```
error[E0308]: mismatched size
 --> test.spl:5:9
  |
5 | process(vec4)
  |         ^^^^ expected `[f64; 3]`, found `[f64; 4]`
  |
  = note: expected fixed-size array `[f64; 3]`
             found fixed-size array `[f64; 4]`
```

### Rule 4: Array Concatenation

```simple
val a: [i64; 2] = [1, 2]
val b: [i64; 3] = [3, 4, 5]
val c = a + b  # What's the type?
```

**Option A: Compile-time size calculation**:
```simple
val c = a + b  # Type: [i64; 5] (2 + 3 = 5)
```

**Option B: Convert to dynamic**:
```simple
val c = a + b  # Type: [i64] (dynamic)
```

**Recommendation**: **Option A** if both sizes are known at compile time, **Option B** otherwise.

---

## Type Inference Rules

### Inference Algorithm

```simple
# 1. Infer from literal:
val arr = [1, 2, 3]
# → Type: [i64] (dynamic by default)

# 2. Infer from annotation:
val vec3: [f64; 3] = [1.0, 2.0, 3.0]
# → Type: [f64; 3] (fixed, size from annotation)

# 3. Infer from function parameter:
fn dot(a: [f64; 3], b: [f64; 3]) -> f64: ...
dot([1.0, 2.0, 3.0], [4.0, 5.0, 6.0])
# → Both literals inferred as [f64; 3]

# 4. Infer from return type:
fn make_vec3() -> [f64; 3]:
    [1.0, 2.0, 3.0]  # Inferred as [f64; 3]

# 5. Infer from usage:
val arr = [1, 2, 3]
arr.push(4)  # Used with push → must be dynamic [i64]
```

### Bidirectional Type Inference

**Top-down** (from annotation/context):
```simple
val vec3: [f64; 3] = [1.0, 2.0, 3.0]  # Type flows down to literal
```

**Bottom-up** (from literal/usage):
```simple
val arr = [1, 2, 3]  # Infer [i64] from literal
arr.push(4)          # Confirm dynamic array from usage
```

**Unification**:
```simple
fn process(v: [f64; 3]) -> [f64; 3]:
    [v[0] + 1.0, v[1] + 1.0, v[2] + 1.0]  # Return type unifies with literal

val result = process([1.0, 2.0, 3.0])  # All types unify to [f64; 3]
```

---

## Runtime Checks (Fallback)

### When Compile-Time Checking Isn't Possible

**Case 1: Dynamic size in function**:
```simple
fn make_array(n: i64) -> [i64]:  # Size unknown at compile time
    [0 for _ in 0..n]

val arr = make_array(5)  # Runtime size: 5

fn needs_three(v: [i64; 3]):
    # ...

needs_three(arr)  # Runtime check: arr.len() == 3?
```

**Runtime error**:
```
RuntimeError: size mismatch in function call
  expected: [i64; 3] (size 3)
  found: [i64] with size 5
  at test.spl:8:13
```

**Case 2: User input**:
```simple
val input = read_array_from_user()  # Unknown size

fn process(v: [f64; 3]):
    # ...

process(input)  # Runtime check
```

### Opt-in Runtime Checks

**Explicit conversion** with runtime validation:
```simple
val arr: [i64] = [1, 2, 3]  # Dynamic array

# Convert to fixed-size with runtime check:
val vec3 = arr.to_fixed::<3>()  # Type: [i64; 3]
# Runtime check: if arr.len() != 3, panic

# Or safe conversion:
val vec3 = arr.try_to_fixed::<3>()  # Type: Result<[i64; 3], SizeError>
match vec3:
    Ok(v): process(v)
    Err(e): print("Size mismatch: {e}")
```

---

## Implementation

### Step 1: Add Fixed-Size Type to Type System (3-4h)

**File**: `rust/compiler/src/types/mod.rs`

```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    // Existing types:
    Array(Box<Type>),  // Dynamic array [T]

    // New: Fixed-size array [T; N]
    FixedArray {
        element_type: Box<Type>,
        size: usize,  // Compile-time constant
    },

    // New: Const fixed-size array
    ConstFixedArray {
        element_type: Box<Type>,
        size: usize,
    },

    // ... other types
}

impl Type {
    pub fn is_fixed_size_array(&self) -> bool {
        matches!(self, Type::FixedArray { .. } | Type::ConstFixedArray { .. })
    }

    pub fn array_size(&self) -> Option<usize> {
        match self {
            Type::FixedArray { size, .. } | Type::ConstFixedArray { size, .. } => Some(*size),
            _ => None,
        }
    }
}
```

### Step 2: Parse Fixed-Size Array Types (2-3h)

**File**: `rust/parser/src/type_parsing/mod.rs`

```rust
// Parse: [T; N]
fn parse_array_type() -> Result<Type, ParseError> {
    expect_token(Token::LeftBracket)?;
    let elem_type = parse_type()?;

    if consume_if_token(Token::Semicolon) {
        // Fixed-size array: [T; N]
        let size_expr = parse_const_expr()?;  // Parse constant expression
        let size = evaluate_const_size(size_expr)?;  // Evaluate at compile time

        expect_token(Token::RightBracket)?;

        Ok(Type::FixedArray {
            element_type: Box::new(elem_type),
            size,
        })
    } else {
        // Dynamic array: [T]
        expect_token(Token::RightBracket)?;
        Ok(Type::Array(Box::new(elem_type)))
    }
}

// Evaluate constant size expression
fn evaluate_const_size(expr: Expr) -> Result<usize, ParseError> {
    match expr {
        Expr::IntLiteral(n) => Ok(n as usize),
        Expr::BinaryOp { op: Op::Add, left, right } => {
            let left_size = evaluate_const_size(*left)?;
            let right_size = evaluate_const_size(*right)?;
            Ok(left_size + right_size)
        }
        _ => Err(ParseError::semantic("array size must be compile-time constant"))
    }
}
```

### Step 3: Type Checking for Fixed-Size Arrays (4-6h)

**File**: `rust/compiler/src/hir/type_checker.rs`

```rust
// Check array literal against expected type
fn check_array_literal(
    elements: &[Expr],
    expected_type: Option<&Type>,
) -> Result<Type, CompileError> {
    let elem_types: Vec<Type> = elements.iter()
        .map(|e| infer_type(e))
        .collect::<Result<_, _>>()?;

    // Unify all element types
    let unified_elem_type = unify_types(&elem_types)?;

    // Check against expected type
    if let Some(expected) = expected_type {
        match expected {
            Type::FixedArray { element_type: expected_elem, size: expected_size } => {
                // Check size match
                if elements.len() != *expected_size {
                    return Err(CompileError::type_error(format!(
                        "mismatched size: expected array of size {}, found size {}",
                        expected_size,
                        elements.len()
                    )));
                }

                // Check element type match
                if !unified_elem_type.is_compatible_with(expected_elem) {
                    return Err(CompileError::type_error("mismatched element type"));
                }

                Ok(Type::FixedArray {
                    element_type: Box::new(unified_elem_type),
                    size: *expected_size,
                })
            }
            Type::Array(_) => {
                // Dynamic array - no size constraint
                Ok(Type::Array(Box::new(unified_elem_type)))
            }
            _ => Err(CompileError::type_error("expected array type"))
        }
    } else {
        // No expected type - default to dynamic array
        Ok(Type::Array(Box::new(unified_elem_type)))
    }
}

// Check method call on fixed-size array
fn check_method_call(
    receiver_type: &Type,
    method_name: &str,
    args: &[Expr],
) -> Result<Type, CompileError> {
    if receiver_type.is_fixed_size_array() {
        // Disallow size-changing methods
        if matches!(method_name, "push" | "pop" | "insert" | "remove" | "clear") {
            return Err(CompileError::type_error(format!(
                "cannot call `{}` on fixed-size array `{}`",
                method_name,
                receiver_type.display()
            )).with_help(format!(
                "`{}` is only available for dynamic arrays `[T]`",
                method_name
            )));
        }
    }

    // Check other methods...
}
```

### Step 4: Runtime Representation (2-3h)

**File**: `rust/compiler/src/value/mod.rs`

```rust
pub enum Value {
    // Dynamic array (existing):
    Array(Rc<RefCell<Vec<Value>>>),

    // Fixed-size array (new):
    FixedArray {
        elements: Rc<RefCell<Box<[Value]>>>,  // Fixed-size slice
        size: usize,  // Redundant but useful for quick checks
    },

    // Const fixed-size array (new):
    ConstFixedArray {
        elements: Rc<Box<[Value]>>,  // No RefCell
        size: usize,
    },

    // ... other variants
}

impl Value {
    pub fn as_array(&self) -> Option<&Rc<RefCell<Vec<Value>>>> {
        match self {
            Value::Array(arr) => Some(arr),
            _ => None,
        }
    }

    pub fn as_fixed_array(&self) -> Option<(&Rc<RefCell<Box<[Value]>>>, usize)> {
        match self {
            Value::FixedArray { elements, size } => Some((elements, *size)),
            _ => None,
        }
    }
}
```

### Step 5: Interpreter Changes (3-4h)

**File**: `rust/compiler/src/interpreter_call/mod.rs`

```rust
Expr::ArrayLiteral { elements } => {
    let values: Vec<Value> = elements.iter()
        .map(|e| evaluate_expr(e, env, ...))
        .collect::<Result<_, _>>()?;

    // Check expected type
    if let Some(Type::FixedArray { size, .. }) = expected_type {
        // Create fixed-size array
        if values.len() != *size {
            return Err(CompileError::runtime(format!(
                "size mismatch: expected {}, found {}",
                size,
                values.len()
            )));
        }

        Ok(Value::FixedArray {
            elements: Rc::new(RefCell::new(values.into_boxed_slice())),
            size: *size,
        })
    } else {
        // Create dynamic array (default)
        Ok(Value::Array(Rc::new(RefCell::new(values))))
    }
}
```

### Step 6: Method Dispatch Updates (2-3h)

**File**: `rust/compiler/src/interpreter_method/collections.rs`

```rust
pub fn call_array_method(
    receiver: &Value,
    method_name: &str,
    args: &[Expr],
    env: &Environment,
) -> Result<Value, CompileError> {
    match receiver {
        Value::Array(arr) => {
            // Dynamic array - all methods allowed
            match method_name {
                "push" => { /* ... */ }
                "pop" => { /* ... */ }
                "len" => Ok(Value::Int(arr.borrow().len() as i64)),
                _ => Err(CompileError::semantic("unknown method"))
            }
        }

        Value::FixedArray { elements, size } => {
            // Fixed-size array - size-changing methods disallowed
            match method_name {
                "push" | "pop" | "insert" | "remove" | "clear" => {
                    Err(CompileError::semantic(format!(
                        "cannot call `{}` on fixed-size array",
                        method_name
                    )))
                }
                "len" => Ok(Value::Int(*size as i64)),
                "get" => { /* indexing allowed */ }
                _ => Err(CompileError::semantic("unknown method"))
            }
        }

        _ => Err(CompileError::type_error("not an array"))
    }
}
```

---

## Examples

### Example 1: 3D Vectors

```simple
# Fixed-size 3D vector type
struct Vec3:
    data: [f64; 3]

    static fn new(x: f64, y: f64, z: f64) -> Vec3:
        Vec3(data: [x, y, z])

    fn dot(other: Vec3) -> f64:
        self.data[0] * other.data[0] +
        self.data[1] * other.data[1] +
        self.data[2] * other.data[2]

    fn cross(other: Vec3) -> Vec3:
        Vec3.new(
            self.data[1] * other.data[2] - self.data[2] * other.data[1],
            self.data[2] * other.data[0] - self.data[0] * other.data[2],
            self.data[0] * other.data[1] - self.data[1] * other.data[0],
        )

# Usage:
val v1 = Vec3.new(1.0, 2.0, 3.0)
val v2 = Vec3.new(4.0, 5.0, 6.0)
print(v1.dot(v2))  # 32.0
```

### Example 2: RGB Colors

```simple
# Fixed-size color type (3 bytes: R, G, B)
type Color = [u8; 3]

val RED: const Color = [255, 0, 0]
val GREEN: const Color = [0, 255, 0]
val BLUE: const Color = [0, 0, 255]

fn blend(c1: Color, c2: Color) -> Color:
    [
        (c1[0] + c2[0]) / 2,
        (c1[1] + c2[1]) / 2,
        (c1[2] + c2[2]) / 2,
    ]

val purple = blend(RED, BLUE)  # [127, 0, 127]
```

### Example 3: Fixed Buffer

```simple
# Fixed-size buffer for data processing
fn process_chunk(buffer: [u8; 1024]):
    # Process exactly 1024 bytes
    for i in 0..1024:
        buffer[i] = transform(buffer[i])

# Compile-time check:
val data: [u8; 1024] = [0; 1024]  # Array of 1024 zeros
process_chunk(data)  # OK

val small_data: [u8; 512] = [0; 512]
process_chunk(small_data)  # ERROR: size mismatch (512 != 1024)
```

### Example 4: Matrix (2D Fixed Array)

```simple
# Fixed-size 3x3 matrix
type Mat3 = [[f64; 3]; 3]

val IDENTITY: const Mat3 = [
    [1.0, 0.0, 0.0],
    [0.0, 1.0, 0.0],
    [0.0, 0.0, 1.0],
]

fn matmul(a: Mat3, b: Mat3) -> Mat3:
    var result: Mat3 = [[0.0; 3]; 3]
    for i in 0..3:
        for j in 0..3:
            for k in 0..3:
                result[i][j] += a[i][k] * b[k][j]
    result
```

---

## Implementation Effort

| Step | Description | Effort |
|------|-------------|--------|
| 1 | Add FixedArray type to type system | 3-4h |
| 2 | Parse `[T; N]` syntax | 2-3h |
| 3 | Type checking for fixed-size arrays | 4-6h |
| 4 | Runtime representation | 2-3h |
| 5 | Interpreter changes | 3-4h |
| 6 | Method dispatch updates | 2-3h |
| 7 | Testing | 2-3h |

**Total**: 18-26 hours

---

## Answer to Your Question

### Q: "can set primitive size fixed array?"
**A**: YES! Use syntax: `val arr: [i64; 3] = [1, 2, 3]`

### Q: "size change cause compile error?"
**A**: YES! Operations like `push()`, `pop()` will cause compile error on fixed-size arrays.

### Q: "type inference to check it compile time possible?"
**A**: YES! Compiler can infer size from:
- Type annotation: `val v: [f64; 3] = [...]`
- Function parameter: `fn f(x: [i64; 5])`
- Literal size: `[1, 2, 3]` has size 3

### Q: "runtime if not possible?"
**A**: YES! When size can't be determined at compile time (e.g., from user input), runtime checks happen automatically with clear error messages.

---

## Integration with Test Fix Plan

**Should we add this to the implementation plan?**

This is a **separate feature** from the test fixes, but could be useful for:
- ML/tensor operations (fixed-size tensors)
- Physics vectors (Vec3, Vec4)
- GPU kernels (fixed buffer sizes)

**Options**:
1. **Add to plan** as Decision #7 (18-26h)
2. **Defer** until after test fixes complete
3. **Implement now** if it helps with specific failing tests

**Your preference?**
