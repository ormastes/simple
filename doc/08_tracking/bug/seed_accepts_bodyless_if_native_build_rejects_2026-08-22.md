# Bodyless `if` block: the two front ends disagree in BOTH directions, and one silently miscompiles

- **Filed:** 2026-08-22
- **Status:** RESOLVED 2026-08-23 — fixed on BOTH front ends; see "Resolution" at the end.
- **Class:** front-end divergence between the seed's Rust parser (`run`/`test`/interpreter)
  and the pure-Simple front end (`native-build`, `src/compiler/10.frontend`).
  Related but NOT the same shape as `hir_unresolved_name_import_reachability_2026-08-22.md`
  and the function-body-local `use` case: those are "seed lenient, stage1 strict".
  **This one is not a one-way leniency gap — neither parser is a superset of the
  other, and the pure-Simple side additionally MISCOMPILES one accepted shape.**

## Symptom

A block header (`if`/`elif`/`else`/`while`/`for`) with no body. What happens
depends on what FOLLOWS the header, and the two front ends disagree in opposite
directions on two of the three shapes.

## Measured truth table

All four fixtures were run end to end on both paths. Native rows are the
**program's output**, not just the exit code.

| # | shape | `bin/simple run` (seed Rust parser) | `bin/simple native-build` (pure-Simple front end) |
|---|---|---|---|
| A | bodyless `if`, next line **DEDENTS** (last stmt of a method) | **ACCEPTS** — empty block, no-op, prints `1` | **parse error**: `line 9:1: unexpected token in expression: Dedent ''` |
| B | bodyless `if`, next line is a **same-column `if`** | ACCEPTS, prints `7` | ACCEPTS, prints `7` — **agree** |
| C | bodyless `if`, next line is a **same-column integer expression** | **REJECTS**: `Unexpected token: expected Indent, found Integer(7)` | **ACCEPTS — and prints `2147483652`, where `7` is correct** |
| — | control (same file, real body) | prints `2` | prints `2` — agree, so the harness is non-vacuous |

Row **A** is seed-lenient / native-strict. Row **C** is the exact opposite —
native-lenient / seed-strict — **and the accepted program is wrong**:
`2147483652` (`0x80000004`) is garbage, not the `7` the function returns.
That is a silent miscompile of malformed source, which is worse than either
parser's rejection.

## Reproduce

`shapeA.spl` (row A):

```
class Probe:
    n: i64

impl Probe:
    me first():
        self.n = 1
        if self.n > 0:

    me second() -> i64:
        self.n

fn main() -> i64:
    var p = Probe(n: 0)
    p.first()
    print p.second()
    0
```

`bodyless.spl` (row C):

```
fn probe(flag: bool) -> i64:
    if flag:

    7

fn main() -> i64:
    print probe(true)
    0
```

Row **B** is *not* a divergence and is explained by the seed's deliberate
**flat-body** feature (a body at the SAME column as the header): the following
`if not flag:` is parsed AS the body. Verified semantically, not by exit code —
both paths print `7`.

## Mechanism (seed side, row A)

`src/compiler_rust/parser/src/parser_impl/core.rs`, `parse_block_after_newline`
(reached for `if`/`elif`/`else`/`while`/`for` via `parse_condition_block`):

1. Next token is not `Indent` → skip blank lines.
2. `is_statement_start()` → parse exactly ONE statement as a *flat body*.
   `is_statement_start` includes `If`, which is why row B is swallowed.
3. **Otherwise `Dedent`/`Eof` → return an EMPTY `Block`, no error.** The in-code
   comment says this arm exists for `case nil:` match arms, but the function is
   shared with `parse_condition_block`, so match-arm leniency leaks into
   conditionals. This is row A.
4. Otherwise → `expect(&TokenKind::Indent)` → the error in row C.

So the seed is already inconsistent with itself: the same empty `if` body is
accepted before a DEDENT and rejected before an integer.

The pure-Simple side of row C (accept + miscompile) is **not yet root-caused** —
it needs its own dig through `src/compiler/10.frontend` block parsing. Stated
here rather than guessed.

## Which parser is right

**Neither, fully.** A bodyless `if` should be a parse error in BOTH — Simple has
`pass` for a deliberate no-op. The pure-Simple side is right on row A, the seed
is right on row C, and row C's native behaviour (accept + emit garbage) is the
single worst cell in the table and should be fixed first.

## Blast radius of making both strict: ZERO in owned code

Scanned **15,190** owned `.spl` files under `src/` (vendored excluded per
CLAUDE.md Owned-Code Scope), skipping docstring bodies:

```
EMPTY-BODY sites in owned .spl (docstrings excluded): 0
```

The only apparent hit before docstrings were excluded was
`src/os/crypto/nacl.spl:175`, `if plain.len() == 0: # auth failed` — which is
**inside a `"""` docstring** (an `Example:` block), not code. So this is not a
latent auth bug, and no owned source depends on either lenient behaviour.

## How it was found

Not by review. While instrumenting HIR lowering for the MirType lane
(`hir_unresolved_type_owner_missing_import_2026-08-22.md`), a script that
stripped probe `eprint`s left their `if` guards behind with no body:

```
             self.symbols.bind_qualified_type(
                 imported_mod.module_name, dependency, terminal_symbol)
+        if hir_module_env_get("SIMPLE_HIR_UNRESOLVED_TYPE_TRACE") == "1":

     me cached_surface_package_name(module_name: text) -> text:
```

The in-process reproducer spec ran **green on that exact tree** and fired 1153
probe lines, so the tree looked validated. `native-build` then died 21 minutes
later with `parse error in .../module_reexport_materialization.spl` and zero
probe output. **A green interpreter run is not a parse gate for native-build.**

## Proposed fix (not landed)

- Seed (row A): thread `allow_empty_body: bool` through
  `parse_block_after_newline`, or split the empty-block arm into a
  `parse_arm_block` used only by match arms. `parse_condition_block` passes
  `false` and errors naming the header; match arms keep the empty arm.
- Pure-Simple (row C): root-cause the accept-and-miscompile first; the fix is
  to reject, matching the seed.

## Why not fixed here

The seed half is a Rust change (`src/compiler_rust`) needing a seed rebuild to
verify, and the shared empty-block arm is load-bearing for `case nil:` match
arms, so it needs its own match-arm regression pass. The native half is not root
caused yet. Neither belongs as a drive-by inside an unrelated HIR-lowering lane;
landing an unverified parser change mid-session is the clobber pattern
`.claude/rules/vcs.md` warns about.

## Fixtures

`.../scratchpad/mt/bodyless/{shapeA,shapeB,bodyless,control}.spl` — promote to
`test/01_unit/language/` when the fix lands, as a parity spec asserting that
BOTH paths reject rows A and C and agree on B and the control.

## Resolution (2026-08-23)

Both halves landed. The agreed rule is the one this record proposed: a
**bodyless block header is a parse error on both paths**, `pass` is the way to
write a deliberate no-op, and the flat-body feature (row B) keeps working.

### Row C — pure-Simple, root cause

`parse_block()` (`src/compiler/10.frontend/core/parser_stmts.spl`) called
`parser_skip_newlines()` unconditionally and then, on anything that was not an
`Indent`, fell straight into "single-line body: parse one statement". It had **no
statement-start gate at all** — the seed's equivalent
(`parse_block_after_newline` -> `is_statement_start`) has one, which is the whole
reason the seed rejects row C and the pure-Simple side did not. So `7` on the
line after a bodyless `if flag:` was swallowed as the if's flat body.

**Where `0x80000004` came from:** nothing was uninitialised in the parser. With
`7` consumed as the if's body, `probe`'s function body is a single `if`
statement and the function has **no tail expression left**, so its `-> i64`
return slot is never written; the caller reads whatever the ABI return register
holds. `2147483652` is that stale value, not a decoded AST node. The AST was
well-formed the whole way down — which is exactly why nothing downstream
complained.

**Fix:** record whether `parse_block()` actually crossed a `Newline` before
skipping. A body on the SAME line as the `:` is untouched (that is the ordinary
`fn f() -> i64: 42` one-liner and it never crosses a newline). A body on a LATER
line at the same column is a flat body and now must open with a real
statement-start token — `parse_block_flat_body_can_start`, mirroring the seed's
`is_statement_start`. Anything else (a literal, a `Dedent`, `Eof`) calls
`parser_expect(181)`, producing `expected Indent, got IntLit '7'` — the same
diagnosis the seed gives.

### Row A — seed

`allow_empty_body` threaded exactly as proposed, with one correction the record
could not have known: match-arm bodies do **not** reach the empty-block arm
through `parse_block`. They arrive via `parse_inline_or_block`
(`parser_helpers.rs`) -> `parse_condition_block`, the same entry point the
conditionals use. Gating only `parse_condition_block` therefore broke trailing
empty `case nil:` arms on the first attempt. The landed shape is
`parse_condition_block_allowing_empty(allow)`: the seven conditional call sites
in `stmt_parsing/control_flow.rs` pass `false` through `parse_condition_block()`,
`parse_inline_or_block` passes `true`, so match arms keep the empty arm.

Also learned while fixturing: an empty `case nil:` arm followed by ANOTHER
`case` has never parsed on either front end (verified against the pre-fix seed:
`expected Indent, found Case`). Only a TRAILING empty arm, i.e. one followed by a
`Dedent`, was ever legal, and that is the shape the regression test pins.

### Post-fix truth table (measured, both paths, program output not exit code)

| # | shape | `run` (seed) | `native-build` (pure-Simple) |
|---|---|---|---|
| A | bodyless `if`, next line DEDENTs | parse error `expected Indent, found Dedent` | parse error `expected Indent, got Dedent ''` |
| B | bodyless `if`, next line same-column `if` | prints `7` | prints `7` |
| C | bodyless `if`, next line same-column integer | parse error `expected Indent, found Integer(7)` | parse error `expected Indent, got IntLit '7'` |
| — | control (real body) | prints `2` | prints `2` |
| — | trailing empty `case nil:` arm | prints `1` (unchanged) | — |

### Blast radius — verified, not assumed

The record's "0 sites in 15,190 owned `.spl`" was re-derived and found **not
directly checkable by text scan**: a naive column heuristic returns 1,702
apparent hits, essentially all of them wrapped multi-line signatures whose
docstring sits at a lower text column than the continuation line but which the
lexer indents normally. Column arithmetic on source text does not model
Indent/Dedent emission, so that scan proves nothing in either direction.

What was measured instead:
- `cargo test --release -p simple-parser`: 302 + ~350 tests green.
  `expression_tests::test_danger_block_is_unsafe_boundary_not_call` fails, and
  was verified failing on the unmodified tree too (pre-existing, unrelated:
  `danger(1)` errors `expected Colon, found Eof`).
- `native-build` with the REBUILT seed: this parses the entire pure-Simple
  compiler and the pulled-in stdlib with the new Rust parser, and the target
  with the new pure-Simple parser. A multi-module fixture (`std.common.text`,
  `std.nogc_sync_mut.fs`, `std.common.json`) reached MIR lowering with **0
  `parser_error` lines**; its failure is a pre-existing unrelated
  `unresolved method call: index_of`.

Residual risk, stated rather than hidden: no full stage1 bootstrap was run, so
the pure-Simple gate has not been exercised over every `src/**.spl`. The gate
only fires for a body on a LATER line at the header's column that opens with a
non-statement token, so a same-line one-liner body — by far the common form —
cannot be affected.

### Gates

- `scripts/check/check-bodyless-block-parity.shs` — runs all four shapes on BOTH
  paths and compares program OUTPUT, not exit status (`run` exits 0 even on a
  parse error). Rows B and D are the non-vacuity guard: a parser that rejects
  everything cannot pass. Verdict convention as in `.claude/rules/vcs.md`:
  `PASS — <n> case(s) checked, 0 divergent` / `FAIL` / `ERROR — nothing was
  checked`; 0 cases or a missing binary is ERROR, never a pass. Measured:
  `PASS — 8 case(s) checked, 0 divergent`.
- `src/compiler_rust/parser/tests/bodyless_condition_block_gate.rs` — six tests:
  bodyless `if` before Dedent / at Eof / before a same-column integer, bodyless
  `while` and `for`, plus POSITIVE assertions that a trailing empty `case nil:`
  arm, the flat body and a real body all still parse.
