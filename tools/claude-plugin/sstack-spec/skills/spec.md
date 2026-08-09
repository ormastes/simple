# SStack Spec Skill — Phase 4: QA Lead (BDD/TDD)

**Trigger:** `/sstack-spec` or when a feature with `Phase: arch-done` needs BDD specs written before code.

## What This Skill Does

Writes failing BDD specs BEFORE any implementation code exists (test-first / Superpowers pattern). Creates SPipe test files at `test/` paths and appends an AC coverage matrix to the state file.

## When to Use

- After Phase 3 (arch) completes with `Phase: arch-done`
- When acceptance criteria need concrete test specs before implementation
- When enforcing test-first discipline

## Workflow

1. Read `.sstack/<feature>/state.md` — extract acceptance criteria, requirements, and architecture
2. For every AC-N, write at least one SPipe `it` block that would verify it
3. Create spec files at `test/` paths mirroring the architecture's module paths
4. Use ONLY built-in SPipe matchers (see below)
5. Every spec MUST fail right now — the code does not exist yet
6. Append the spec file list and coverage matrix to the state file

## SPipe Matchers (ONLY these)

```simple
expect(actual).to_equal(expected)
expect(actual).to_be(expected)           # identity check
expect(actual).to_be_nil()
expect(actual).to_contain(element)
expect(actual).to_start_with(prefix)
expect(actual).to_end_with(suffix)
expect(actual).to_be_greater_than(n)
expect(actual).to_be_less_than(n)
```

Do NOT use: `to_be_true`, `to_be_false`, `to_raise`, `to_match`, or any custom matchers.
Use `to_equal(true)` and `to_equal(false)` instead.

## SPipe File Structure

```simple
use std.spec

describe "<ModuleName>":
    describe "<function_or_behavior>":
        it "<AC-N: what should happen>":
            # Arrange
            val input = ...
            # Act
            val result = function_under_test(input)
            # Assert
            expect(result).to_equal(expected_value)
```

## Boundaries (Boil a Small Lake)

- ONLY test specs
- Do NOT implement the feature
- Do NOT modify architecture
- Do NOT fix failing specs by writing production code — they MUST fail
- Context budget: sub-40%

## Entry Criteria

- `.sstack/<feature>/state.md` exists with `Phase: arch-done`
- Architecture and requirements are present
- Module paths and public API signatures are defined

## Exit Criteria

- Spec files exist at `test/` paths for every module in the architecture
- Every AC-N has at least one `it` block
- All specs use only built-in matchers
- All specs WOULD FAIL (no implementation exists yet)
- State file contains `## Specs` with file list and AC coverage matrix
- `## Phase` updated to `spec-done`

## State File Additions

```markdown
## Specs

### Spec Files
- `test/path/feature_spec.spl` — N specs covering AC-1, AC-2
- `test/path/module_spec.spl` — N specs covering AC-3
- ...

### AC Coverage Matrix
| AC | Spec File | it block | Status |
|----|-----------|----------|--------|
| AC-1 | `test/path/feature_spec.spl` | "should do X" | Failing (no impl) |
| AC-2 | `test/path/feature_spec.spl` | "should do Y" | Failing (no impl) |
| ...  | ... | ... | ... |

## Phase
spec-done

## Log
- intake: Created state file with N acceptance criteria
- research: Found N reusable modules, N existing files, N requirements drafted
- arch: Designed N modules, N decisions, no circular deps
- spec: Created N spec files with N total specs, 100% AC coverage
```

## Next Phase

Implementation can now begin -- all specs are in place as the acceptance gate.
