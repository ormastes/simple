# Generic-argument lookahead: separator ratchet ordered ahead of argument-continuing tokens

- **Date:** 2026-08-24
- **Status:** FIXED (this change) — the defective form was never committed; it
  was caught as an uncommitted working-tree edit before it could land.
- **Scope:** self-hosted front end only (`src/compiler/10.frontend/core/parser_expr.spl`,
  `try_skip_ident_generic_args()`). The Rust seed parser is unaffected.
- **Severity:** would have been a compiler-wide parse regression — a broken
  generic-argument lookahead breaks every build.

## Background: the incident that was NOT this one

A stage-3 phase-2 run failed on `src/app/office/sheets/data_ops.spl:38:33`:

```
if key_col < 0 or key_col > (max_col - min_col):
```
```
parse error — const generic arguments are not supported (Tensor<i64, 2>)
```

That is **already filed and already fixed**:

- `doc/08_tracking/bug/parser_comparison_chain_misread_as_generic_args_2026-08-18.md`
- `doc/08_tracking/bug/parser_lt_gt_or_misparsed_as_generic_args_2026-08-21.md`
- fix `bf440c278b8`, spec `test/01_unit/compiler/parser_comparison_chain_not_generic_args_spec.spl`

`Tensor<i64, 2>` is a canned EXAMPLE string inside the diagnostic, not anything
in the offending source. The stage-3 failure came from a **deployed stage binary
built before `bf440c278b8`**, not from a defect in `main`. Measured on this
tree (see Evidence): the exact `data_ops` shape parses clean at HEAD.

## The actual defect recorded here

A proposed change extended the separator ratchet
(`const_arg_needs_separator`) so it arms after **every** complete generic
argument — idents and keyword type names, not only numeric literals — to close
the ident-only variant `a < b or a > (c)`, which HEAD's numeric-only ratchet
never arms for and therefore silently CONFIRMS as generic arguments.

The intent is right. The **branch order** was wrong. In the `while` walk the
armed-ratchet `break` sat BEFORE the argument-continuing tokens:

```
elif const_arg_needs_separator:
    break
elif k == 6:                      # ident, arms the ratchet
...
elif (k == 62 or k == 120 ...):   # * & [ ( . ::  — continuation
```

So once an ident armed the ratchet, the very next `*`, `::`, `.` or `[` — all of
which continue the SAME type — hit the armed break and backtracked a genuine
generic instantiation into a comparison.

The Rust twin (`src/compiler_rust/parser/src/expressions/postfix.rs`,
`try_skip_ident_generic_args`) does not have this problem because it arms
`need_comma` after a whole `parse_type()`, which itself consumes `*`, `&`, `::`,
`.` and `[...]`. "Arm after every ident" is therefore **not** parity with the
seed; the Simple side is a flat token walk with no type-level grouping, so the
continuation tokens must be handled explicitly and BEFORE the ratchet.

## Fix

Branch order in `try_skip_ident_generic_args()` is now:

1. `TOK_INT_LIT` (armed check internal)
2. `>` / `>>` / `<` / `,`
3. **argument-CONTINUING tokens** `* & [ ( . ::` — clear the ratchet
4. **argument-COMPLETING tokens** `] ) ?` — arm the ratchet
5. armed-ratchet `break`
6. `TOK_IDENT` — arm
7. keyword type names (20-59) — arm
8. else `break`

`]` `)` `?` must also precede the armed break, or `foo<[T]>(x)` breaks at `]`.

## Evidence

In-process probe driving the SELF-HOSTED front end via `parse_full_frontend`
(`bin/simple` is the Rust seed, so running a `.spl` through it exercises the
Rust parser, not this file; the tracked stage binaries currently SEGV).
`OK` = parses clean, `ERR` = parser reported an error.

| case | HEAD | proposed edit | fix |
|---|---|---|---|
| `if a < 0 or a > (b - c)` (the data_ops shape) | OK | OK | OK |
| `a < b or a > (c)` | OK | OK | OK |
| `a < b and c > d` | OK | OK | OK |
| `foo<std::Bar>(1)` | OK | OK | OK |
| **`foo<T*>(1)`** | OK | **ERR** | OK |
| `foo<[T]>(1)` | OK | OK | OK |
| `foo<Bar.Baz>(1)` | OK | OK | OK |
| `make<Dict<String, Array<i64>>>(1)` | OK | OK | OK |
| `a<b>(c)` | OK | OK | OK |
| `Tensor<i64, 2>(1)` (must stay rejected) | ERR | ERR | ERR |

### Corpus check — ATTEMPTED AND DISCARDED, not evidence

A wider check (80 real `.spl` sources containing `> (` or `<T>(`, parsed through
the same in-process route) was built and run, then **discarded as unsound**:
`parser_error_count()` is not a monotone process-wide counter — it resets per
parse, so the per-file *delta* the probe recorded produced negative values and
attributed errors to the wrong files. No conclusion is drawn from it, and none
is claimed. A corrected corpus check would record the ABSOLUTE per-file count;
it is not supplied here.

## Known limitation, stated rather than papered over

The ident-only chain `a < b or a > (c)` parses **clean under both readings** —
as a comparison chain and as the call `a<b or a>(c)` — so this harness cannot
distinguish them by parser-error state alone. The ratchet tightening is
therefore justified by parity with the Rust twin and by the corpus being
unchanged, NOT by a discriminating test. A discriminating test needs AST
introspection and is not supplied here.

## Gate

`scripts/check/check-generic-arg-lookahead.shs` — fail-closed, `--selftest`
runs first and is fatal, verdict is the last line of stdout, a 0-case run is
ERROR. It pins both failure directions (too permissive, too strict).

Measured verdict lines (2026-08-24, this tree, `bin/simple` = Rust seed
interpreting the self-hosted front end; exit status read directly into a
variable, never through a pipe):

```
$ sh scripts/check/check-generic-arg-lookahead.shs --selftest
PASS — 3 case(s) checked, selftest only (harness discriminates clean vs broken)
EXIT=0

$ sh scripts/check/check-generic-arg-lookahead.shs          # with the fix
PASS — 10 case(s) checked, 0 mismatches (self-hosted generic-argument lookahead)
EXIT=0

$ sh scripts/check/check-generic-arg-lookahead.shs          # with the DEFECTIVE edit
FAIL — 10 case(s) checked, pointer_arg(expected=OK,got=ERR)
EXIT=1
```

The third run is the load-bearing one: the gate is proved to CATCH the defect
it was written for, not merely to be green next to it.
