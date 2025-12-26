# Unit Arithmetic Design

## Overview

This document describes the grammar and semantics for:
1. **Type-safe unit arithmetic** - Prevent invalid operations like `km + hr`
2. **Compound units** - Derived units like `m/s`, `kg*m/s²`
3. **Custom unit operations** - User-defined functions like `log`, `exp`

## Grammar

### 1. Unit Family with Arithmetic Rules

```ebnf
unit_family_def = "unit" IDENT "(" "base" ":" type ")" ":" variant_list [ ":" NEWLINE INDENT arithmetic_block DEDENT ]

variant_list = variant ("," variant)*
variant = IDENT "=" NUMBER

arithmetic_block = arithmetic_rule+
arithmetic_rule = binary_rule | unary_rule | custom_fn

binary_rule = "allow" binary_op "(" type_param ")" "->" type_result
unary_rule = "allow" unary_op "->" type_result
custom_fn = "fn" IDENT "(" params ")" [ "->" type ] ":" NEWLINE INDENT body DEDENT

binary_op = "add" | "sub" | "mul" | "div" | "mod"
unary_op = "neg" | "abs"
```

### 2. Compound Unit Definition

```ebnf
compound_unit_def = "unit" IDENT "=" unit_expr [ ":" NEWLINE INDENT arithmetic_block DEDENT ]

unit_expr = unit_term (("*" | "/") unit_term)*
unit_term = IDENT [ "^" INTEGER ]
```

### 3. Examples

#### Basic Unit Family with Arithmetic Rules

```simple
unit length(base: f64): m = 1.0, km = 1000.0, cm = 0.01:
    # Type-safe: length + length -> length
    allow add(length) -> length
    allow sub(length) -> length

    # Scaling: length * number -> length
    allow mul(f64) -> length
    allow div(f64) -> length

    # Unary operations
    allow neg -> length
    allow abs -> length

    # Custom operations (return raw value, loses unit)
    fn log(self) -> f64:
        return log(self.value())

    fn exp(self) -> f64:
        return exp(self.value())

    fn sqrt(self) -> f64:
        return sqrt(self.value())
```

#### Time Unit Family

```simple
unit time(base: f64): s = 1.0, ms = 0.001, hr = 3600.0:
    allow add(time) -> time
    allow sub(time) -> time
    allow mul(f64) -> time
    allow div(f64) -> time
    allow neg -> time
    allow abs -> time
```

#### Compound Units (Derived Units)

```simple
# Velocity = length / time
unit velocity = length / time:
    allow add(velocity) -> velocity
    allow sub(velocity) -> velocity
    allow mul(f64) -> velocity
    allow div(f64) -> velocity

    # velocity * time -> length
    allow mul(time) -> length

# Acceleration = velocity / time = length / time²
unit acceleration = length / time^2:
    allow add(acceleration) -> acceleration
    allow sub(acceleration) -> acceleration
    allow mul(f64) -> acceleration

    # acceleration * time -> velocity
    allow mul(time) -> velocity

# Force = mass * acceleration (Newton's second law)
unit mass(base: f64): kg = 1.0, g = 0.001, lb = 0.453592

unit force = mass * acceleration:
    allow add(force) -> force
    allow sub(force) -> force
    allow mul(f64) -> force
    allow div(f64) -> force
```

#### Usage Examples

```simple
unit length(base: f64): m = 1.0, km = 1000.0:
    allow add(length) -> length
    allow mul(f64) -> length

unit time(base: f64): s = 1.0, hr = 3600.0:
    allow add(time) -> time

# Valid operations
let d1 = 5_km
let d2 = 3_km
let total = d1 + d2      # OK: length + length -> length
let scaled = d1 * 2.0    # OK: length * f64 -> length

let t1 = 2_hr
let t2 = 1_hr
let duration = t1 + t2   # OK: time + time -> time

# Invalid operations (compile error)
let invalid = d1 + t1    # ERROR: cannot add length + time
let bad = d1 * d2        # ERROR: length * length not allowed (need explicit rule)
```

## Semantics

### Type Checking Rules

1. **Binary Operations**
   - `a + b` requires `allow add(typeof(b)) -> result` in `typeof(a)`'s unit family
   - `a - b` requires `allow sub(typeof(b)) -> result`
   - `a * b` requires `allow mul(typeof(b)) -> result`
   - `a / b` requires `allow div(typeof(b)) -> result`

2. **Automatic Unit Conversion**
   - Operations between same-family units auto-convert to base unit
   - `5_km + 3000_m` → converts both to meters, result in base unit

3. **Compound Unit Resolution**
   - `velocity = length / time` creates implicit conversion rules
   - `length / time` produces `velocity`
   - `velocity * time` produces `length`

### Default Arithmetic (No Rules Specified)

If a unit family has no arithmetic block, **no arithmetic is allowed** by default:
```simple
unit user_id(base: u64): uid = 1
# user_id + user_id -> ERROR (no rules defined)
```

### Primitive Interop

Units can always:
- Convert to their base type via `.value()` method
- Be created from literals with suffix
- Be compared with `==`, `!=`, `<`, `>`, `<=`, `>=` (same family only)

## Implementation Notes

### Parser Changes

1. Extend `UnitFamilyDef` AST node:
```rust
pub struct UnitFamilyDef {
    pub name: String,
    pub base_type: Type,
    pub variants: Vec<UnitVariant>,
    pub arithmetic: Option<UnitArithmetic>,  // NEW
}

pub struct UnitArithmetic {
    pub binary_rules: Vec<BinaryArithmeticRule>,
    pub unary_rules: Vec<UnaryArithmeticRule>,
    pub custom_fns: Vec<FunctionDef>,
}

pub struct BinaryArithmeticRule {
    pub op: BinaryOp,
    pub operand_type: Type,
    pub result_type: Type,
}
```

2. Add `CompoundUnitDef` AST node:
```rust
pub struct CompoundUnitDef {
    pub name: String,
    pub expr: UnitExpr,
    pub arithmetic: Option<UnitArithmetic>,
}

pub enum UnitExpr {
    Base(String),
    Mul(Box<UnitExpr>, Box<UnitExpr>),
    Div(Box<UnitExpr>, Box<UnitExpr>),
    Pow(Box<UnitExpr>, i32),
}
```

### Interpreter Changes

1. Store arithmetic rules in `UnitFamilyInfo`
2. Check rules during binary/unary operations on `Value::Unit`
3. Return appropriate error for disallowed operations

### Error Messages

```
error: cannot add `length` and `time`
  --> example.spl:10:15
   |
10 | let x = d1 + t1
   |              ^^ `time` cannot be added to `length`
   |
   = help: `length` only allows: add(length) -> length
   = note: different unit families cannot be combined
```

## Future Extensions

1. **Dimensional Analysis** - Automatic compound unit inference
2. **SI Prefix Support** - Auto-detect kilo, mega, etc.
3. **Unit Aliases** - `type Distance = length` with same rules
4. **Generic Units** - `unit Container[T](base: T)`
