# Language Feature Tests

**Purpose:** Specification tests for proposed language features
**Status:** Skip tests (features not yet implemented)
**Last Updated:** 2026-01-06

This directory contains comprehensive BDD-style specification tests for proposed language features documented in [`doc/research/code_shortening_grammar_analysis.md`](../../../doc/research/code_shortening_grammar_analysis.md).

## Test Status

All tests in this directory are marked with `skip: true` until the corresponding features are implemented.

## Features Covered

### Tier 1: Essential Features (High Priority)

| Test File | Feature | Operator | Priority | Tests |
|-----------|---------|----------|----------|-------|
| [`error_propagation_spec.spl`](error_propagation_spec.spl) | Error propagation | `?` | 🥇 1 | Result/Option propagation |
| [`optional_chaining_spec.spl`](optional_chaining_spec.spl) | Optional chaining | `?.` | 🥈 2 | Safe navigation |
| [`nullish_coalescing_spec.spl`](nullish_coalescing_spec.spl) | Nullish coalescing | `??`, `??=` | 🥉 3 | Default values |
| [`pipeline_operator_spec.spl`](pipeline_operator_spec.spl) | Pipeline operator | `\|>` | 4 | Data flow transformation |
| [`placeholder_argument_spec.spl`](placeholder_argument_spec.spl) | Placeholder argument | `_` | 5 | Concise lambdas |

### Unified Design Features

| Test File | Feature | Syntax | Phase | Tests |
|-----------|---------|--------|-------|-------|
| [`expression_bodied_functions_spec.spl`](expression_bodied_functions_spec.spl) | Expression functions | `=>`, `=>:` | Phase 2 | Function brevity |
| [`for_while_expressions_spec.spl`](for_while_expressions_spec.spl) | Loop expressions | `for ... =>` | Phase 3 | Yieldable loops |
| [`switch_expressions_spec.spl`](switch_expressions_spec.spl) | Switch expressions | `case ... =>` | Phase 4 | Pattern matching values |

## Test Organization

Each spec file follows BDD structure:

```simple
describe "Feature Name":
    context "Specific aspect":
        it "does something", skip: true:
            # Test code
            expect(result).to_equal(expected)
```

### Test Categories per File

Each spec file includes:

1. **Basic usage** - Core functionality examples
2. **Type system integration** - Type inference and checking
3. **Chaining/composition** - Combining with other features
4. **Edge cases** - Boundary conditions and error handling
5. **LOC reduction** - Before/after comparisons
6. **Desugaring** - How syntax translates to implementation

## Running Tests

**Current status:** All tests skipped (features not implemented)

Once features are implemented:

```bash
# Run all language feature tests
cargo test -p simple-driver simple_stdlib_language

# Run specific feature test
cargo test -p simple-driver simple_stdlib_language_error_propagation_spec

# Run with interpreter
./target/debug/simple simple/std_lib/test/language/error_propagation_spec.spl
```

## Implementation Tracking

### Phase 1: Error/Optional Handling (Sprint 1-2)

- [ ] Error propagation `?` operator
  - [ ] Parser: Postfix `?` operator
  - [ ] Type checker: Result/Option compatibility
  - [ ] Codegen: Desugar to match + early return
  - [ ] Tests: Remove `skip: true` from `error_propagation_spec.spl`

- [ ] Optional chaining `?.` operator
  - [ ] Parser: `?.` chain operator
  - [ ] Type checker: Propagate Option through chain
  - [ ] Codegen: Desugar to nested matches
  - [ ] Tests: Remove `skip: true` from `optional_chaining_spec.spl`

- [ ] Nullish coalescing `??` and `??=`
  - [ ] Parser: `??` binary operator
  - [ ] Parser: `??=` assignment operator
  - [ ] Type checker: Option[T] ?? T → T
  - [ ] Codegen: Desugar to match/conditional
  - [ ] Tests: Remove `skip: true` from `nullish_coalescing_spec.spl`

### Phase 2: Dataflow (Sprint 3-4)

- [ ] Pipeline operator `|>`
  - [ ] Parser: `|>` binary operator
  - [ ] Type checker: Thread types through pipeline
  - [ ] Codegen: Desugar to nested calls
  - [ ] Tests: Remove `skip: true` from `pipeline_operator_spec.spl`

- [ ] Placeholder argument `_`
  - [ ] Parser: `_` in arg position
  - [ ] Type checker: Create implicit lambda
  - [ ] Codegen: Generate lambda parameter
  - [ ] Tests: Remove `skip: true` from `placeholder_argument_spec.spl`

### Phase 3: Unified Design - Functions (Sprint 5)

- [ ] Expression-bodied functions
  - [ ] Parser: `fn ... => expr` and `fn ... =>: block`
  - [ ] Type checker: Last value rule
  - [ ] Codegen: Desugar to block with return
  - [ ] Tests: Remove `skip: true` from `expression_bodied_functions_spec.spl`

### Phase 4: Unified Design - Loops (Sprint 6)

- [ ] For/while expressions
  - [ ] Parser: `for ... =>` and `for ... =>:`
  - [ ] Type checker: Yieldable[T] type
  - [ ] Codegen: Desugar to map/flatMap/withFilter
  - [ ] Tests: Remove `skip: true` from `for_while_expressions_spec.spl`

### Phase 5: Unified Design - Switch (Sprint 7)

- [ ] Switch expressions
  - [ ] Parser: `case ... =>` arms
  - [ ] Type checker: Exhaustiveness + type consistency
  - [ ] Codegen: Expression-valued match
  - [ ] Tests: Remove `skip: true` from `switch_expressions_spec.spl`

## Documentation Generation

These spec files are designed to:

1. **Serve as executable documentation** once implemented
2. **Generate API docs** showing usage examples
3. **Validate implementation** against spec

To generate docs (once implemented):

```bash
# Generate documentation from specs
cargo test --doc

# View generated examples
open target/doc/simple/index.html
```

## Contributing New Tests

When adding tests for new features:

1. Create `<feature>_spec.spl` in this directory
2. Mark all tests with `skip: true`
3. Add header comment with:
   - Feature description
   - Status (NOT IMPLEMENTED)
   - Priority tier
   - Tracking link to research doc
4. Update this README with new entry
5. Follow BDD structure (describe/context/it)

## Related Documentation

- **Research:** [`doc/research/code_shortening_grammar_analysis.md`](../../../doc/research/code_shortening_grammar_analysis.md)
- **Spec:** [`doc/spec/syntax.md`](../../../doc/spec/syntax.md)
- **Grammar:** [`doc/spec/parser/lexer_parser_grammar_expressions.md`](../../../doc/spec/parser/lexer_parser_grammar_expressions.md)
- **Testing Guide:** [`doc/guides/test.md`](../../../doc/guides/test.md)

---

**Total:** 7 spec files, 100+ skip tests, covering 8 major language features
