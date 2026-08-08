# Counted `for i in 0..N` loops used as unbounded parser scan loops

**Status:** Swept (preventive) — no reachable cap demonstrated
**Date:** 2026-08-01
**Area:** `src/compiler/10.frontend/` (parser + lexer)
**Predecessor:** `doc/08_tracking/bug/parser_array_literal_element_cap_2026-08-01.md`
(commit `55115a82411`), which fixed two members of this family after a real
production failure, and enumerated the siblings as "unreachable today but the
same latent defect". This document closes the family and records that the
siblings do indeed appear to be unreachable — the attempt to demonstrate
otherwise failed, and that failure is written up below because it cost a day.

## The defect shape

A parser scan loop walks a token run whose length the source decides. Writing it
as `for i in 0..N:` puts a hard cap on the number of loop passes. When the cap is
reached the loop simply falls out: nothing is reported, the cursor is left parked
mid-construct, and the next `parser_expect(...)` blames whichever perfectly
well-formed token it happens to be looking at. That silence is what made the
array-literal instance expensive to diagnose.

The bound counts **loop passes**, not the entity being parsed, so the size at
which a construct breaks depends on how many tokens each pass retires.

## Enumeration

`/usr/bin/grep -rnE 'for [A-Za-z_][A-Za-z0-9_]* in 0\.\.[0-9]{3,}' src/compiler/10.frontend/`
finds **118 loops**. (Use `/usr/bin/grep` explicitly — the default `grep` on this
machine is ugrep and has disagreed on this pattern.)

| bound | count |
|------:|------:|
| `0..100`     | 40 |
| `0..1000`    | 25 |
| `0..10000`   | 22 |
| `0..100000`  | 19 |
| `0..200`     |  7 |
| `0..1000000` |  3 |
| `0..1024`    |  2 |
| **total**    | **118** |

| file | loops |
|------|------:|
| `core/parser_expr.spl` | 23 |
| `core/lexer_struct.spl` | 22 |
| `core/parser_stmts.spl` | 12 |
| `core/parser_decls_use.spl` | 10 |
| `core/_ParserPrimary/primary_expr.spl` | 9 |
| `core/_ParserDecls/enum_module_body.spl` | 9 |
| `core/_ParserDecls/fn_struct_decls.spl` | 7 |
| `core/parser_decls_fn.spl` | 5 |
| `core/parser.spl` | 4 |
| `core/_ParserPrimary/asm_match_suffix.spl` | 3 |
| `core/parser_decls_types.spl` | 3 |
| `core/parser_cli.spl` | 3 |
| `core/parser_asm.spl` | 3 |
| `core/parser_preprocessor.spl` | 2 |
| `core/_ParserDecls/bitfield_aop_arch_decls.spl` | 2 |
| `desugar/spawn_analysis.spl` | 1 |
| `core/_ParserPrimary/asm_raw_parsing.spl` | 1 |
| `core/lexer.spl` | 1 |

**All 118 are scan loops; none is a genuine bounded iteration, so none was left
alone.** In 110 the loop variable is never read in the body — it is a pure pass
counter. In the other 8 it is read only for a trace message (`i={i}`), for a
first-iteration guard (`if ci > 0:`), or to mint a unique reserved-field name
(`int_to_str(bf_i)`). Not one of the 118 indexes a fixed-size collection.

A caution for anyone sizing the risk from the bound alone: many of the `0..100`
loops are *inner* comma-skip loops that normally run one or two passes, not
per-item loops. The bound is not a limit on the construct's element count.

## No reachable cap was demonstrated

This is a negative result, recorded so it is not re-investigated from scratch.

Probed against the pure-Simple frontend, each fixture in **its own process**:
150-parameter function, 150-parameter generic, 1500-field struct, 1500-arm
`match`, 1500-variant enum, 1500 module declarations, 1500 block statements,
1500 `impl` methods, 150-item `use` list, 1100 string interpolations, 60-deep
nested blocks, 10050 call arguments, 151 chained `??`, 151 chained `<`, 151
chained `<<`, 1501 chained `+`, 1501 chained `*`, 250-segment `use` path, 1500
chained member accesses, 1500 chained index expressions, 1500 chained calls.
**Every one parses clean on the unmodified parser.** The two 10050-element
literal fixtures from the predecessor fix also parse clean, confirming that fix
still holds.

### The harness trap that produced a false RED

An earlier run of the same fixture set reported five failures on the unmodified
parser, which flipped to clean after the sweep. That result was an artifact and
is retracted.

`parse_module_silent_checked` does **not** reset parser and AST state between
calls, so parsing many files in one process accumulates state and the per-file
verdict depends on what was parsed before it. The five failures came from
passing all seventeen fixtures to one process. Re-running the identical
fixture, byte for byte, one process per file, passes; and re-running the
original all-in-one-process shape later did not reproduce the failures on the
unmodified parser either. A verdict from this oracle is only meaningful with
one process per fixture.

The generic lesson: an oracle that shares global state across inputs will
manufacture input-order-dependent verdicts that look exactly like a size cap.

## Change

All 118 loops become unbounded; termination is structural rather than counted.

* 110 loops: `for V in 0..N:` becomes `while true:`.
* 8 loops that read `V`: `var V: i64 = 0 - 1` before the loop, `while true:`,
  and `V = V + 1` as the first body statement. The increment sits at the top so
  it also runs on the `continue` paths, which a bottom increment would skip.

`while` was already the idiom here, not a novelty: `primary_expr.spl:476` used
`while par_kind_get() == 160:` before this sweep, and both loops fixed by
`55115a82411` are `while` forms.

### Termination

Every converted loop retires at least one token (or one source byte) per pass
from a finite stream that ends in EOF, which no arm consumes. The bodies fall
into three proof shapes:

1. **Operator / separator climb** — most of `parser_expr.spl`, plus
   `parser_asm.spl` and `asm_match_suffix.spl`:
   `if <kind>: parser_advance(); ... else: break`. Every non-breaking arm opens
   with `parser_advance()`. Checked individually for `parser_expr.spl` lines
   280, 346, 380, 396, 479, 512, 534, 542, 739 and the two postfix loops at 859
   and 1058, whose `continue` paths all sit after a `parser_advance()` and whose
   `elif` chains all end in `else: break`.
2. **Item list** — `parser_decls_use.spl`, `enum_module_body.spl`,
   `fn_struct_decls.spl`, `parser_decls_fn.spl`, `parser_decls_types.spl`:
   break on the closing bracket and on EOF, otherwise consume the item and its
   separator.
3. **Character scan** — the 22 loops in `lexer_struct.spl`: the witness is the
   byte cursor (`self.pos` or a local `pos`), not the token cursor. Each pass
   either calls `self.advance()` / `pos = pos + 1` or breaks, and every one
   breaks on `pos >= src_len` / `self.at_end()`.

Three item-list loops had a static gap: a token that is neither a terminator,
nor a name, nor a comma would leave the cursor unmoved — harmless under the old
counted form (it spun out the bound and fell through), but a hang under an
unbounded `while`.

* `parser_decls_use.spl` import list (`use a.{...}`)
* `parser_decls_use.spl` export brace list (`export X.{...}`)
* `enum_module_body.spl` export-from list

Each now ends with an `elif not <consumed>: parser_advance()` error-recovery
arm, matching the `else: parser_advance()` already present in
`parser_decls_types.spl:145` and `enum_module_body.spl:154`.

**No input that reaches those three stalls was found.** Nine candidate stalling
tokens (`*`, `+`, `=`, `[`, a number, a string, and mid-list variants) were
tried against a transform-only tree with the recovery arms removed; all nine
completed. The hazard is read off the source, not demonstrated. The arms are
defensive and cannot alter any path that already made progress.

## Evidence

Oracle: a probe calling `parse_module_silent_checked(source, path)` from
`compiler.core.parser`, run as `./bin/simple probe_parse.spl <fixture>` — a bare
positional `.spl` is what reaches the pure-Simple frontend. One process per
fixture, for the reason above.

Traps worth restating: `simple compile` exits 0 on a compile failure, and
invoked by **absolute path** it exits 0 without compiling at all. Neither exit
status is evidence. `--entry X` delegates to the Rust seed. `simple_seed test`
runs the tree-walking interpreter and says nothing about compiled lanes.

* **Equivalence sweep** over all 11,310 `.spl` files under `src/compiler`,
  `src/app` and `src/lib`, unmodified versus swept, 40 chunks of 379 files with
  one process per chunk: identical FAIL sets. (A single-process sweep over all
  11,310 was tried first and died at 6 GB RSS from unbounded AST accumulation —
  another consequence of the missing inter-file reset.)
* **Cap matrix**, 17 fixtures, one process each, unmodified versus swept: all
  clean on both sides, including the predecessor's two 10050-element literals as
  positive controls.
* **Per-item probes**, 10 further fixtures targeting the precedence-climb and
  postfix loops specifically: all clean on the unmodified parser.
* Hang probes for the three recovery arms complete rather than time out.

## Regression coverage

None added. `test/01_unit/compiler/parser/large_collection_literal_spec.spl`
was extended with fixtures for four suspected boundaries and then reverted: with
the harness trap corrected the fixtures parse clean on the unmodified parser, so
they were vacuous and would have been false coverage. The existing spec already
covers the one boundary in this family that was ever shown to be real.

A spec that would genuinely cover the remaining 116 loops needs an input that
trips one of them, and this lane did not find one.
