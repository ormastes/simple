# Test Agent - Writing and Running Tests

**Use when:** Writing new tests, fixing failing tests, running test suite, analyzing test results.
**Skills:** `/test`, `/spipe`

## Quick Start

```simple
# test/my_feature_spec.spl
describe "MyFeature":
    context "when initialized":
        it "has default value":
            expect(0).to_equal(0)

    context "with operations":
        before_each:
            var counter = 0

        it "increments":
            counter = counter + 1
            expect(counter).to_equal(1)
```

Run: `bin/simple test test/my_feature_spec.spl`

## Built-in Matchers (ONLY these work)

| Matcher | Usage |
|---------|-------|
| `to_equal(val)` | `expect(x).to_equal(5)` |
| `to_be(val)` | `expect(x).to_be(5)` |
| `to_be_nil` | `expect(x).to_be_nil` |
| `to_contain(item)` | `expect(list).to_contain(5)` |
| `to_start_with(s)` | `expect(str).to_start_with("hi")` |
| `to_end_with(s)` | `expect(str).to_end_with("lo")` |
| `to_be_greater_than(n)` | `expect(x).to_be_greater_than(5)` |
| `to_be_less_than(n)` | `expect(x).to_be_less_than(10)` |

**NOT available:** `to_be_true()`, `to_be_false()`, `to eq()`, `.new()` constructors

## Common Anti-Patterns (AVOID)

- `expect(x).to_equal(y))` - extra `)` at end
- `.to_be_true()` - use `.to_equal(true)` instead
- `.to_be_false()` - use `.to_equal(false)` instead
- `.to eq(` - use `.to_equal(` instead
- `ClassName.new(args)` - use `ClassName(field: value)` instead

## Test Types

- `it "name":` - Regular test (runs by default)
- `slow_it "name":` - Slow test (run with `--only-slow`)
- `skip_it "name":` - Skipped in interpreter, runs in compiled mode

## Hooks

- `before_each:` - Runs before each test (outer -> inner)
- `after_each:` - Runs after each test (inner -> outer)

## Test File Structure

```
test/
  std/          # Stdlib tests
  lib/          # Library tests
  app/          # App tests
  compiler/     # Compiler tests
```

Files: `*_spec.spl` or `*_test.spl`

## Import System for Tests

1. Ensure the source module exists under `src/lib/`.
2. Use curly brace syntax: `use std.module.{func1, func2}`
3. Functions accessible directly: `func1()`, `func2()`

## Running Tests

```bash
bin/simple test                          # All tests
bin/simple test path/to/spec.spl         # Single file
bin/simple test doc/path/guide.md        # Markdown doctests
bin/simple test --spl-doctest src/path/module.spl # Source documentation tests
bin/simple test --refresh-manifest       # Refresh after bulk moves/edits
bin/simple test --list                   # List tests
bin/simple test --only-slow              # Slow tests only
```

## Documentation Tests

- Markdown: closed, non-empty `simple`, `spl`, or `sdoctest` fences; configured
  repository discovery is owned by `config/sdoctest.sdn`.
- Simple source: closed, non-empty fences in `#`, `##`, or `///` comments,
  fenced blocks inside triple-quoted docstrings, and docstring `sdoctest:`
  sections.
- Use a `text` fence for illustrative code that must not execute. Use `:skip`
  only for a registered example that is intentionally unavailable.
- Registration must call the same extractor used by execution. Do not add a
  separate regex-only counter; it will drift from modifiers and comment forms.
- Run an edited doctest file explicitly. Whole-release evidence remains
  `bin/simple test test --whole --mode=interpreter`.

## Critical Rules

- NEVER add `#[ignore]` without user approval
- NEVER skip failing tests as a "fix"
- ALWAYS fix root cause or ask user
- One assertion concept per test
- Use docstrings (`"""..."""`) for test documentation, NOT println()

## See Also

- `/spipe` - Full SPipe BDD framework guide
- `/test` - Test methodology and coverage
- `.claude/templates/spipe_template.spl` - Template for new specs
