# Bug — Interpreter rejects `!` (unwrap) operator on variables and in non-terminal positions

**Filed:** 2026-05-08 (debug format library test failures)
**Severity:** High — blocks any interpreter-mode code using `variable!`, `x!.field`, or `fn(expr!)` patterns.

## Symptom

```
Error: parse error: function arguments: expected Comma, found Bang
Error: parse error: Unexpected token: expected '(', '{', or '[', found Newline
```

The interpreter rejects `!` (unwrap operator) in these cases:

### Case A: Bare variable unwrap (even at statement end)
```spl
val x: i64? = 42
val y = x!          # FAILS: "expected '(', '{', or '[', found Newline"
```

### Case B: Unwrap in member-access chains
```spl
val y = best!.address   # FAILS
```

### Case C: Unwrap inside function arguments
```spl
expect(result.err()!)   # FAILS: "expected Comma, found Bang"
return Err(x.err()!)    # FAILS
```

**Working:** `result.ok()!` and `result.err()!` at statement end (method-call unwrap only).

Lint (`bin/simple build lint`) accepts ALL forms without errors.

## Root Cause (Hypothesis)

The interpreter parser only handles `!` as a postfix operator after method-call expressions (`.method()!`). It does not handle `!` after:
- Bare identifiers (`variable!`)
- Any expression when followed by `.`, `)`, or `,`

Likely location: `src/compiler_rust/compiler/src/interpreter/` or `src/compiler_rust/compiler/src/parser/` — the expression parser's postfix-operator handling.

## Workaround

For Case A: Use `if val` pattern binding instead of `!`:
```spl
# Before (fails):
val f = found!

# After (works):
if val f = found:
    expect(f.tag).to_equal(0x2e)
```

For Case C: Extract method-call unwrap to a temp var:
```spl
# Before (fails):
expect(result.err()!).to_contain("bad magic")

# After (works):
val err_msg = result.err()!
expect(err_msg).to_contain("bad magic")
```

## Affected Files (Workarounds Applied)

All files below have been patched to use the workaround patterns.

### Test files
| File | Lines | Original Pattern |
|------|-------|-----------------|
| `src/lib/nogc_sync_mut/debug/formats/test/dwarf_abbrev_spec.spl` | 75-79 | `found!`, `found!.tag` |
| `src/lib/nogc_sync_mut/debug/formats/test/msf_parser_spec.spl` | 10, 26 | `result.err()!` in fn args |

### Library files
| File | Lines | Original Pattern |
|------|-------|-----------------|
| `src/lib/nogc_sync_mut/debug/formats/dwarf_parser.spl` | 559, 564 | `best!.address`, `best!.location` |
| `src/lib/nogc_sync_mut/debug/formats/pdb_parser.spl` | 283, 288 | `best!.address`, `best!.location` |
| `src/lib/nogc_sync_mut/debug/formats/msf_parser.spl` | 165 | `Err(header_result.err()!)` |
| `src/compiler/70.backend/linker/macho_inspect.spl` | 144 | `Err(header_result.err()!)` |
| `src/compiler/70.backend/linker/macho_parser.spl` | 312 | `Err(inspect_result.err()!)` |
| `src/compiler/70.backend/linker/pe_inspect.spl` | 247 | `Err(header_result.err()!)` |
| `src/compiler/70.backend/linker/pe_parser.spl` | 266 | `Err(inspect_result.err()!)` |
| `src/lib/nogc_sync_mut/debug/formats/pdb_parser.spl` | 152, 162 | `Err(msf_result.err()!)`, `Err(dbi_result.err()!)` |

## Proposed Fix

Update the interpreter expression parser to:
1. Allow `!` after any expression (not just method calls)
2. Allow `!` to be followed by `.` (member access), `)` (closing paren), and `,` (argument separator)

## Related Bugs

- `interpreter_parser_enum_match_and_it_block_regressions_2026-05-02.md` — similar parser strictness mismatch between lint and interpreter
- `feedback_simple_parser_strict_callsites.md` (memory) — documents broader pattern of interpreter rejecting valid syntax
