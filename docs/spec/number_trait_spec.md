# number_trait_spec

*Source: `simple/std_lib/test/features/stdlib/number_trait_spec.spl`*

---

Number Trait - Feature #1003

Overview:
    Number trait providing a unified interface for numeric types (i64, f64).
    Enables generic programming over numbers with methods like zero(), one(),
    abs(), signum(), and conversions. Common interface for both integer and
    floating-point types.

Syntax:
    val x: i64 = -42
    x.abs()          # 42
    x.signum()       # -1
    x.is_negative()  # true

    val y: f64 = -3.14
    y.abs()          # 3.14
    y.to_i64()       # -3

Implementation:
    - Number trait implemented for i64 and f64
    - Static methods: zero(), one()
    - Instance methods: abs(), signum()
    - Predicates: is_zero(), is_positive(), is_negative()
    - Conversions: to_i64(), to_f64()
    - f64::to_i64() truncates toward zero
    - Handles edge cases: negative zero, large integers

Notes:
    - The Number trait provides a common interface for both integer and
      floating-point types, enabling generic numeric algorithms
    - Enables writing generic functions over numeric types
