# Bug: self-hosted parser caps array and dict literals at 10000 commas

- **ID:** parser_array_literal_element_cap_2026-08-01
- **Date:** 2026-08-01
- **Status:** FIXED
- **Component:** `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl`
- **Severity:** High — a valid, committed, generated source file is unparseable
  by the self-hosted compiler, so the self-hosted and seed frontends disagree on
  what the language accepts.

## Symptom

```
[parser_error] path src/lib/common/web/public_suffix_data.spl line 10012:25: expected ], got , ','
```

The comma the parser complains about is perfectly well-formed, and so is every
token around it. Nothing in the diagnostic hints that a size limit was reached,
which is what made this expensive to chase: the message points at valid syntax
and invites you to go looking for a lexer or grammar defect that does not exist.

The error is followed by a long cascade of
`unexpected token in expression: , ','`, one per remaining element, as the
parser tries to resume statement parsing from the middle of the literal.

## Root cause

`parse_primary_expr` walked the elements of an array literal with a **counted**
loop:

```
var elements: [i64] = [first_elem]
for i in 0..10000:
    if par_kind_get() != 160:
        break
    parser_advance()
    if par_kind_get() == 145:
        break
    elements.push(parse_expr())
parser_expect(145)
```

The loop is bounded at 10000 passes and each pass consumes exactly one comma.
When a literal carries more commas than that, the loop simply *falls out* — it
reports nothing — leaving the cursor parked on the next comma. The
`parser_expect(145)` on the following line is what finally speaks up, and it
names the token it happens to be looking at rather than the limit that was
actually hit. The dict-literal loop 220 lines further down had the identical
`for i in 0..10000` bound and the identical failure mode.

This is not an allocation cap, a fixed-size buffer, or a counter overflow. It is
a hard-coded iteration bound, and it counts **commas consumed**, not elements
stored — a distinction that is directly observable (below).

## Bisected boundary — PROVED

Measured with stage2 self-hosted binaries built from the pristine tree and from
the patched tree, invoked with a **bare positional path**
(`simple compile --format=smf <file>`), which reaches the pure-Simple
`CompilerDriver`. `--entry` was deliberately not used: it delegates to the Rust
runtime and does not exercise the Simple parser at all.

Two fixture shapes, identical except for the last element:

- `tc` — trailing comma after every element including the last, the shape
  generated tables use. N elements, N commas.
- `ntc` — no trailing comma after the last element. N elements, N-1 commas.

| shape | N     | pristine | patched |
|-------|-------|----------|---------|
| tc    | 3     | OK       | OK      |
| tc    | 1000  | OK       | OK      |
| tc    | 5000  | OK       | OK      |
| tc    | 9000  | OK       | OK      |
| tc    | 9999  | OK       | OK      |
| tc    | 10000 | **OK**   | OK      |
| tc    | 10001 | **FAIL** | OK      |
| tc    | 10002 | FAIL     | OK      |
| tc    | 20000 | FAIL     | OK      |
| ntc   | 9999  | OK       | OK      |
| ntc   | 10000 | OK       | OK      |
| ntc   | 10001 | **OK**   | OK      |
| ntc   | 10002 | **FAIL** | OK      |
| ntc   | 10003 | FAIL     | OK      |

**The boundary is 10000 commas.** That is 10001 elements with no trailing comma
and 10000 elements with one.

`ntc` at 10001 passes while `tc` at 10001 fails — the same element count, a
different comma count. That rules out a cap on the number of elements *stored*
and confirms the bound is on loop passes. 10000 is an arbitrary decimal
constant, not a power of two, which independently rules out an i32/u16 counter
overflow or a fixed-size buffer.

### Ruled out: per-line and per-token budgets

A 10050-element array packed **50 elements per line** (10049 commas, ~210 lines)
fails on the pristine binary too, at `line 202:10`. The same 10050 elements one
per line fail at `line 10002:10`. Both fail at their 10001st element regardless
of how many lines or tokens preceded it, so neither a per-line nor a per-token
budget is involved. Only the comma count matters.

### The arithmetic predicts the real failure site exactly

`PUBLIC_SUFFIX_EXACT_RULES` opens on line 11 and its first element is on line 12,
so pass `i` pushes the element on line `13 + i`. The last pass (`i = 9999`)
pushes the element on line 10012 — the 10001st — and the loop then falls out with
the cursor on that element's trailing comma at column 25. That is
`line 10012:25`, character for character the reported diagnostic.

## Fix

Both loops become unbounded `while` loops. Termination is structural rather than
counted, and each is safe because every pass retires at least one token from a
finite stream:

- **Array literal** — `while par_kind_get() == 160:`. The loop is entered only
  when the cursor is on a comma, and its first action is an unconditional
  `parser_advance()` that consumes that comma. Progress is therefore strictly
  monotone even when the element expression that follows is malformed and
  `parse_expr()` consumes nothing. At EOF the token kind is 190, never 160, so
  the loop exits.
- **Dict literal** — `while true:`. Every path through the body either `break`s
  outright (on `}`, or via the `expected , or } in dict literal` error path,
  which is what EOF takes) or consumes the comma via `parser_advance()`.

The `while par_kind_get() == 160:` form is not novel here — the paren/tuple
element loop at line 476 of the same file already used exactly it. The two
counted loops were the outliers.

## Verification

- Regression spec: `test/01_unit/compiler/parser/large_collection_literal_spec.spl`
  — a 10050-element array literal and a 10050-pair dict literal, both past the
  bound. The spec file is itself unparseable by the pristine self-hosted parser
  (`line 274:10: expected ], got , ','`) and parses with zero diagnostics after
  the fix.
- `public_suffix_data.spl`, the file that first surfaced this, goes from the
  reported error to zero parser diagnostics.
Measured numbers, same binaries, same relative paths:

| file | pristine | patched |
|------|----------|---------|
| `large_collection_literal_spec.spl` | 299 diagnostics, first `line 274:10` | **0** |
| `public_suffix_data.spl` | 821 diagnostics, first `line 10012:25` | **0** |

- Revert-proof: the two stage2 binaries were built from the same worktree, the
  pristine one from the blob `cff98f1fb349cc1fb9e8cfcf0b627c700785b827` confirmed
  identical to the one at the remote tip. The pristine binary reproduces the
  originally reported error character for character, so the failure is
  demonstrably restored by reverting the patch alone.
- **Whole-closure parse regression check:** the patched compiler was itself used
  to build stage2 over `--entry-closure` across `src/compiler`, `src/app` and
  `src/lib` — **728 modules compiled, 0 failed**, byte-identical module count and
  outcome to the pristine build (also 728/0). Every `.spl` file in the compiler's
  own import closure therefore parses exactly as it did before. This is a far
  broader no-regression signal than a hand-picked file list.
- A narrower parse sweep over the 45 real `.spl` sources carrying the largest
  collection literals was also started; it was still in flight when this was
  landed and is superseded by the whole-closure result above.

### Harness trap worth knowing

Passing an **absolute** path to `simple compile` makes the driver report
`error: in-process SMF compile: native entry source not found: <path>` and exit
**without compiling**. Grepping that output for `[parser_error]` yields nothing,
which is indistinguishable from a clean parse. An early run of the regression
spec scored as passing on the *pristine* binary for exactly this reason. Use a
relative path from the worktree root, and treat "no diagnostics" as a result only
after confirming the compile actually ran.

## Frontend disagreement — INFERRED, not measured

`public_suffix_data.spl` is a committed, generated source that the production
tree builds through the Rust seed, so the seed evidently does not share this
bound. That is an inference from the file being in-tree and buildable; the seed
parser was not directly bisected here.

## Sibling caps NOT fixed

`for i in 0..10000` and `for i in 0..100000` appear in roughly twenty more places
across `10.frontend/core` — `parser_stmts.spl`, `parser_decls_use.spl`,
`parser_expr.spl`, `parser_asm.spl`, `parser.spl`, `lexer_struct.spl`. Each is
the same latent shape: a counted loop standing in for a `while`, which will
silently truncate and then blame an innocent token once real input exceeds the
bound. None is reachable by any source in the tree today, so none is fixed here,
but they are the same defect waiting for a large enough input. Converting them is
tracked separately rather than bundled into this fix.
