# try_operator_spec

*Source: `simple/std_lib/test/features/stdlib/try_operator_spec.spl`*

---

Try Operator (?) - Feature #204

Overview:
    The ? operator for Result/Option propagation. Unwraps Ok(value)/Some(value)
    or early-returns Err(e)/None. Enables clean error handling without explicit
    match statements. Familiar syntax for Rust developers.

Syntax:
    fn compute(a: i64, b: i64, c: i64) -> Result<i64, text>:
        step1 = divide(a, b)?  # Returns Err if b == 0
        step2 = divide(step1, c)?
        return Ok(step2)

Implementation:
    - Postfix operator on Result/Option values
    - Unwraps Ok(value) or Some(value) to value
    - Propagates Err(e) or None via early return
    - Works in function returns
    - Preserves error types through propagation
    - Parsed as postfix operator with correct precedence
    - Supports chaining multiple ? operators
    - Short-circuits on first error

Notes:
    - Familiar syntax for Rust developers
    - Reduces error handling boilerplate significantly
    - Composes well with other operators
