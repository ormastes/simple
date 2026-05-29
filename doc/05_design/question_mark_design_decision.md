# Design Decision: Question Mark (`?`) Usage

**Status:** Final
**Date:** 2026-01-18
**Decision:** `?` is NOT allowed in method/function/variable names

## Summary

The `?` character is reserved for operators only and cannot be used in identifiers (method names, function names, variable names). This differs from Ruby, which allows `?` as a suffix for predicate methods.

## Context

Some languages (notably Ruby) use `?` as a suffix for predicate methods:
```ruby
# Ruby style (NOT supported in Simple)
def empty?
  @items.length == 0
end
```

However, Simple uses `?` for several operator purposes that would conflict with this naming convention.

## Decision

**`?` is reserved for operators only:**

1. **Try Operator (implemented):** `result?` - Error propagation for Result/Option
   ```simple
   fn read_config() -> Result<Config, Error>:
       val contents = read_file(path)?   # Early return on error
       val parsed = parse(contents)?
       return Ok(parsed)
   ```

2. **Optional Type Syntax (implemented):** `T?` - Sugar for `Option<T>`
   ```simple
   fn find_user(id: i64) -> User?:
       return users.get(id)
   ```

3. **Optional Chaining (planned):** `obj?.field` - Safe navigation
   ```simple
   val name = user?.profile?.name   # Returns None if any part is None
   ```

4. **Nullish Coalescing (planned):** `a ?? b` - Default on None
   ```simple
   val name = user?.name ?? "Anonymous"
   ```

## Rationale

1. **Async/Await Confusion:** Using `?` in method names would be confusing in async contexts where `?` is used for error propagation.

2. **Parser Complexity:** Supporting `?` in identifiers would require context-sensitive parsing to distinguish between `obj.method?()` (method named `method?`) vs `obj.method()?` (try operator on result).

3. **Consistency with Rust:** Simple follows Rust's error handling patterns, where `?` is exclusively an operator.

4. **Clear Predicate Convention:** Use `is_*` prefix instead:
   ```simple
   # Correct: Use is_* prefix for predicates
   fn is_empty() -> bool:
       return self.len == 0

   fn is_valid() -> bool:
       return self.validate().is_ok()
   ```

## Identifier Syntax

Valid identifiers in Simple:
```
identifier: [a-zA-Z_][a-zA-Z0-9_]*
```

Characters NOT allowed in identifiers:
- `?` - Reserved for operators
- `!` - Reserved for macros
- `-` - Would conflict with subtraction
- `@` - Used for decorators

## Migration from Ruby-style Code

If porting code from Ruby that uses `?` suffix:

| Ruby | Simple |
|------|--------|
| `empty?` | `is_empty()` |
| `valid?` | `is_valid()` |
| `nil?` | `is_none()` |
| `include?` | `contains()` |
| `exist?` | `exists()` |

## Tests

Parser tests verify this behavior:
- `src/parser/tests/error_tests.rs`:
  - `test_question_mark_not_allowed_in_function_name`
  - `test_question_mark_not_allowed_in_method_name`
  - `test_question_mark_not_allowed_in_variable_name`
  - `test_question_mark_valid_as_try_operator`
  - `test_question_mark_valid_as_optional_type`

## References

- [API Design: Predicate Naming](improve_api.md) - `is_*` convention
- [Code Shortening Grammar](../research/code_shortening_grammar_analysis.md) - Try operator status
- [Rust Error Handling](https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html)
