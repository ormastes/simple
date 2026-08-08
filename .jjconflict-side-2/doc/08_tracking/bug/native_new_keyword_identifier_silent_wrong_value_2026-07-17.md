# Native path: `new` used as a plain identifier silently evaluates to the wrong value (and crashes when used as a method arg)

**Date:** 2026-07-17
**Severity:** High (silent wrong output with no diagnostic; escalates to SIGSEGV)
**Status:** source fixed for unambiguous terminal references; dual-backend execution pending
**Task:** #178 native text interpolation + string ops verification round 2 (lane S47)

## Symptom

The seed oracle (`bin/simple run`) accepts `new` as an ordinary local-variable
name (it is not a hard keyword in that grammar/runtime). The native
(pure-Simple) path tokenizes `new` unconditionally as `TOK_KW_NEW`
(`src/compiler/10.frontend/core/tokens.spl:180`, `const TOK_KW_NEW: i64 = 211`)
with no contextual fallback to a plain identifier in expression position. The
two paths then disagree in two different, inconsistent ways depending on
*where* the reference appears:

1. **Inside string interpolation** (`"{new}"`): compiles successfully and
   prints a nonsense value with **no diagnostic at all** — a silent wrong
   answer.
2. **As a call argument** (`show(new)`): fails with a **loud** parse error
   (`unexpected token in expression: )`).

Both are the *same* underlying identifier reference; the two call sites just
disagree on whether the malformed `new`-expression parse is allowed to fall
through silently or not.

## Repro 1 — silent wrong value via interpolation

```simple
fn main():
    val new = "L"
    print "NV:{new}|END"
```

- Oracle (`bin/simple run`): `NV:L|END`
- Native (`native-build`, `SIMPLE_BOOTSTRAP` unset): `NV:3|END`

No error, no warning — just a different value substituted in place of the
variable's actual content.

## Repro 2 — loud parse error via direct reference

```simple
fn show(x: text):
    print x

fn main():
    val new = "L"
    show(new)
```

- Oracle: prints `L`.
- Native: `native-build` fails to compile:
  ```
  [parser_error] line 6:13: unexpected token in expression: ) ')'
  [parser_error] line 6:14: expected ), got Newline ''
  error: native-build failed without diagnostics
  ```

## Repro 3 — real-world consequence: SIGSEGV in `.replace()`

Found while regression-checking `.replace()` (task #178 round 1 fixed the
receiver/arg string-tagging for `starts_with`/`replace`/etc.). Passing a
variable named `new` as the replacement argument crashes the native binary:

```simple
fn main():
    val a = "hello"
    val new = "L"
    print "O5:{a.replace(\"l\", new)}|END"
```

Native run:
```
[simple-runtime] Fatal: SIGSEGV at address 0x3
```

**Confound ruled out:** this is NOT an independent `.replace()` bug. Renaming
the same variable to a non-keyword name (`repl`) with everything else
identical reproduces correctly on both oracle and native:

```simple
val repl = "L"
print "R:{a.replace(\"l\", repl)}|END"   # -> "R:heLLo|END" on BOTH paths
```

The crash is fully explained by the `new`-identifier bug: whatever
placeholder value `new` lowers to inside the malformed-but-silently-accepted
expression parse gets treated downstream as a real operand (likely a raw,
untagged small integer standing in for a string handle). When that bogus
value is passed to a runtime string function expecting a tagged string
pointer, dereferencing it faults. This is consistent with the crash address
literally being `0x3` — the same small placeholder magnitude class as the
`3` printed in Repro 1 (not verified as the exact same constant; not required
to pin down the mechanism to file this).

## Expected

`new` should either:
- be usable as an ordinary identifier everywhere (matching the oracle), with
  the `new`-expression grammar production only kicking in when it is
  syntactically followed by a type name (contextual keyword, same shape as
  the existing `grid` contextual-keyword fix in
  `parser_grid_identifier_keyword_collision_2026-07-03.md`); or
- if `new` must remain a hard keyword, every use site must fail the same way
  — loudly, at parse or lowering time — never silently substitute a
  placeholder value. The string-interpolation sub-parser's fallback-to-literal
  path (used elsewhere for other malformed placeholder expressions, see
  `interp_brace_literal_collides_with_string_interpolation_2026-07-03.md`)
  should trigger the same loud error class here instead of accepting a
  malformed `new`-expression and lowering it to a placeholder constant.

## Suggested direction

- Check whether `val new = ...` binding-name parsing already special-cases
  keyword tokens as valid binding names (it must, since Repro 1/3 compile) and
  make expression-position identifier parsing symmetric with that, OR
- Locate the `new`-expression grammar production (imported via `TOK_KW_NEW` in
  `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` and
  `src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl`) and ensure
  a malformed/incomplete `new`-expression (no type name/args following) is a
  hard parse error surfaced through every call site that reaches it,
  including inside string-interpolation sub-parsing.

## Verification

- `new_keyword_identifier` is a strict LLVM/Cranelift parity case covering
  interpolation, a direct function argument, and a `.replace(..., new)`
  operand. It is selected on macOS, Windows, and FreeBSD as well as the full
  Linux gate.
- The parser now treats `new` as an identifier when the following token is an
  unambiguous expression terminator. It deliberately preserves the documented
  generic `new expr` allocation grammar. Ambiguous postfix forms such as
  `new[...]` versus `new [ ... ]` still require a separate grammar decision;
  adopting the Rust parser's allocation-start allowlist here would silently
  narrow `doc/05_design/runtime/explicit_allocation_design.md`.
- Source/static gates may pass without executing Simple; native dual-backend
  execution is required before marking this bug closed.

- Reproduced on worktree `/home/ormastes/dev/wt_r_find_infer` at tip
  `ffc0c360ba4` (fetched 2026-07-17), using
  `env -u SIMPLE_BOOTSTRAP bin/simple run` (oracle) and
  `env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH bin/simple native-build`
  (native).
- Confound test (non-keyword variable name in the same `.replace()` shape)
  passes on both oracle and native, isolating the defect to the `new`
  identifier specifically.
