# Newline Migration Plan - Replace "\n" with NL/"{NL}"

**Date:** 2026-02-13
**Status:** Planning
**Scope:** 925 files, 7,502 occurrences

## Objective

Replace all hardcoded `"\n"` string literals with the `NL` constant from `src/lib/text.spl` for better maintainability and cross-platform compatibility.

## Strategy

1. **Import NL constant** - Add `use std.text.{NL}` to files that need it
2. **String interpolation** - Use `"{NL}"` in interpolated strings
3. **String concatenation** - Use `NL` directly in non-interpolated contexts
4. **Preserve** - Keep `\n` in raw strings, comments, docstrings, char_code lookups

## Replacement Rules

| Context | Before | After |
|---------|--------|-------|
| Interpolated string | `"error:\nDetails"` | `"error:{NL}Details"` |
| String concat | `text + "\n"` | `text + NL` |
| Split operation | `.split("\n")` | `.split(NL)` |
| Join operation | `.join("\n")` | `.join(NL)` |
| Function call | `fn("\n")` | `fn(NL)` |
| Char literal check | `c == "\n"` | `c == NL` |

## Exceptions (Do NOT change)

1. **src/lib/text.spl** - NL constant definition itself (lines 113-114, 122-126, 410, 410)
2. **test files** - Newline constant tests (test_newline_*.spl, newline_constants_spec.spl)
3. **Raw strings** - `r"regex\n"` patterns
4. **Comments** - `# Example: "hello\n"`
5. **Docstrings** - Documentation examples
6. **Assembly generation** - Direct `.text\n` for ASM output
7. **Escape sequence tables** - char_code/char_from_code mapping tables

## Work Division (6 agents in parallel)

### Agent 1: src/compiler/ (200 files)
- Focus: linker/, loader/, backend/, driver.spl
- Files: ~150 occurrences

### Agent 2: src/compiler_core_legacy/ (250 files)
- Focus: All compiler_core_legacy modules
- Files: ~300 occurrences

### Agent 3: src/app/ (150 files)
- Focus: cli/, mcp/, io/, test_runner_new/
- Files: ~200 occurrences

### Agent 4: src/lib/ (200 files)
- Focus: All stdlib modules (EXCEPT text.spl)
- Files: ~250 occurrences

### Agent 5: test/compiler/ + test/unit/ (200 files)
- Focus: Compiler and unit tests
- Files: ~150 occurrences

### Agent 6: test/feature/ + test/integration/ (125 files)
- Focus: Feature and integration tests
- Files: ~100 occurrences

## Implementation Steps

For each agent:

1. **Search** - Find all `"\n"` in assigned directory
2. **Analyze** - Categorize by context (interpolated vs concat vs preserve)
3. **Add imports** - Add `use std.text.{NL}` to files needing it
4. **Replace** - Apply replacements following rules above
5. **Verify** - Check no syntax errors introduced

## Testing Strategy

1. **Run tests** - `bin/simple test` after each agent completes
2. **Regression check** - Ensure 604/604 tests still pass
3. **Build check** - `bin/simple build` succeeds

## Estimated Impact

- **Files modified:** ~850 (excluding exceptions)
- **Lines changed:** ~7,000
- **Imports added:** ~850 `use std.text.{NL}` lines
- **Build time:** No change (constant folding)
- **Runtime:** No change (NL = "\n" at compile time)

## Success Criteria

- ✅ All `"\n"` replaced except documented exceptions
- ✅ All 604 tests still pass
- ✅ Build succeeds without warnings
- ✅ No functional changes to behavior
