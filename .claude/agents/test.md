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

## SSpec documentization gate

For changed SSpec/manual pairs, run `simple sspec-maintain scan <spec>` and
review all seven scores, blockers, stable findings, mirror state, and REQ
traceability. Scaffolds preserve source hash/REQ IDs and fail fast until real
assertions exist. `improve` requires exact confirmation and rollback;
`documentize` reuses SPipe.

## Every fix ships a reproduction spec AND similar-case specs

A bug fix without tests is unverified; a fix with only the one reproducing
example is under-verified. Mandatory for every bug fix:

1. **Reproduction spec, red-first.** Write the example that reproduces the
   reported symptom, run it, and OBSERVE it fail with that exact symptom
   BEFORE fixing. After the fix, re-run and report both observations
   (`red: <failing values> → green: N/N`). A spec written after the fix may
   assert something that was already true — it proves nothing.
2. **Similar-case specs.** The defect's SHAPE usually exists in sibling code
   paths: the other variants of the same match, the other members of the same
   API family, the other axis values of the same config, boundary neighbors
   (0/1/max, empty/single/many). Add examples for the nearest siblings —
   grep for the pattern that was wrong and cover each place it repeats. A
   fix that closes one arm and leaves its twins untested invites the same
   bug back one door over.
3. **Sabotage check.** Re-break the fix (or an equivalent mutation), confirm
   the new specs go red, restore, confirm green. Report green→red→green.

If a reproduction genuinely cannot be automated (external hardware, timing),
say so in the bug doc and record the manual repro steps — never silently skip.
