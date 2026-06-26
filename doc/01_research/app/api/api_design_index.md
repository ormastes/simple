# Simple Standard Library API Design

Comprehensive API design guidelines based on lessons learned from Rust, Python, Ruby, Scala, Go, and Java.

## Documentation Structure

- [Option/Result API](api_design/option_result.md) - Error handling patterns
- [Naming Conventions](api_design/naming.md) - Consistent naming across the stdlib
- [Collections API](api_design/collections.md) - Array, dict, set design
- [String API](api_design/strings.md) - String manipulation
- [Numeric API](api_design/numerics.md) - Math and numeric types
- [Error Handling](api_design/errors.md) - Error patterns and best practices
- [I/O API](api_design/io.md) - File and network I/O
- [Concurrency API](api_design/concurrency.md) - Async, actors, channels
- [Testing API](api_design/testing.md) - Test framework design
- [Documentation Standards](api_design/documentation.md) - Docstring conventions
- [Ruby-Inspired Features](api_design/ruby_features.md) - Convenience features from Ruby
- [Python-Inspired Features](api_design/python_features.md) - Convenience features from Python  
- [Best Practices](api_design/best_practices.md) - Combined lessons from all languages
- [Design Principles](api_design/principles.md) - Core API design principles

## Quick Reference

### Core Principles
1. **Explicit over implicit** - No hidden panics
2. **Consistent naming** - `to_*` (convert), `as_*` (view), `into_*` (consume)
3. **Safe by default** - Unsafe operations clearly marked
4. **Zero-cost abstractions** - High-level APIs compile to efficient code
5. **Discoverable** - IDE autocomplete-friendly naming

### Common Patterns
- **Error handling**: `expect(msg)` not `unwrap()`
- **Iteration**: Both `iter()` and `each()` for Ruby/Python ergonomics
- **Conversion**: `to_string()` (allocate), `as_str()` (borrow)
- **Construction**: Builder pattern for complex types
- **Testing**: BDD `describe/it` and doctest `>>>` examples

See [Architecture](../architecture/overview.md) for module organization.
