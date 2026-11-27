# Angle-Bracket Index Lint Parse Mismatch

Date: 2026-06-06

Status: Closed 2026-11-25 — lint side was wrong; the defective suggestion existed
only in the Rust seed and is already fixed there (see resolution below).

## Summary

The compiler warning for bracket array indexing says to use angle-bracket
syntax such as `next_depth<cpu>`, but the parser rejects that expression form in
normal boolean conditions.

## Repro

In `src/os/kernel/scheduler/green_carrier.spl`, changing:

```spl
next_depth[cpu] > 0
```

to:

```spl
next_depth<cpu> > 0
```

and running:

```sh
SIMPLE_LIB=/tmp/simple-cooperative-green/src /tmp/simple-cooperative-green/src/compiler_rust/target/debug/simple check src/os/kernel/scheduler/green_carrier.spl test/01_unit/os/kernel/scheduler/green_carrier_spec.spl
```

failed with:

```text
error[E0002]: unexpected token
  expected: expression
  found:    Gt
```

## Impact

Carrier queue code must keep bracket indexing for now even though interpreter
test output emits a deprecation warning. This is a grammar/lint mismatch, not a
green-carrier behavior issue.

## Required Fix

Either make angle-bracket value indexing parse in expression contexts, or update
the warning so it does not recommend syntax that the parser rejects.

## Re-verification / triage (2026-08-09)

Re-ran both halves of the repro against current `bin/simple`
(`bin/release/x86_64-unknown-linux-gnu/simple`, seed):

- `bin/simple check src/os/kernel/scheduler/green_carrier.spl` still emits the
  lint `Use angle brackets: next_depth<...> instead of next_depth[...]` (and
  several sibling identifiers in the same file/other files), confirming the
  warning is still live.
- A minimal file with `next_depth<cpu> > 0` in a boolean condition still fails
  to parse: `error: ... Unexpected token: expected expression, found Gt`.

Both sides of the mismatch still reproduce exactly as documented — not a stale
defect. `/usr/bin/grep -rln "Use angle brackets" src/` finds the message text
only inside `src/compiler_rust/target/**` build artifacts and
`src/compiler_rust/lib/std/src/parser/error_recovery.spl` (also under
`src/compiler_rust/`) — the lint's source of truth lives entirely under the
Rust seed tree.

Per this sweep's scope rules (no edits under `src/compiler_rust/**`), this
defect is left **OPEN / out of scope for this sweep**. No source changes made.

## Resolution (2026-11-25)

**Which side was wrong: the lint.** Angle-bracket value indexing (`a<i>`) is
not valid Simple. In expression position, `<` after an identifier is either
the less-than operator or a generic-argument list, and the latter only when
the closing `>` is followed by `.` or `(` (method call / struct literal).
Both parsers implement exactly this rule:

- pure-Simple: `src/compiler/10.frontend/core/parser_expr.spl`
  `try_skip_ident_generic_args()` — confirms generic args only when the token
  after `>` is `TOK_DOT` or `TOK_LPAREN`, backtracks to less-than otherwise.
- Rust seed: `src/compiler_rust/parser/src/expressions/postfix.rs`
  `try_parse_ident_generic_args()` — same commit/backtrack rule.

So the parser's rejection of `next_depth<cpu> > 0`
(`Unexpected token: expected expression, found Gt`) is correct behavior, and
the lint's advice was the defect: following it broke working code. The
accepted index form is and remains `next_depth[cpu]`.

**Where the defect lived: the Rust seed only.** The suggested text
(`Use angle brackets: {name}<...> instead of {name}[...]`) is emitted from
`src/compiler_rust/parser/src/parser_types.rs` (type-parameter position) and
leaked into expression contexts when a speculative generic-argument parse
pushed the hint as a side effect and backtracked only token state. The
pure-Simple compiler never contained this lint text — grep for
"Use angle brackets" under `src/compiler` finds nothing; its
`src/compiler/10.frontend/parser/recovery.spl` `WrongBrackets` hint covers
generic *type parameter* lists only, where `<...>` is genuinely accepted.
Per repo policy the seed is bootstrap-only, so no Rust patch was made in this
sweep; the concrete seed fix is recorded here instead.

**The concrete seed fix (already landed before this sweep):**

- `0f5b67b79b4` (2026-08-17): both speculative generic-arg parses in the
  seed's `postfix.rs` now save `error_hints.len()` and truncate on backtrack,
  so an abandoned speculation can no longer leak the deprecation hint.
  Sibling record:
  `doc/08_tracking/bug/parser_bracket_index_after_less_than_still_misread_as_generics_2026-08-17.md`.
- `734edf2819f` (2026-08-25): `detect_common_mistake_lookahead` adds two
  suppress-only discriminators (what follows the name; SCREAMING_SNAKE_CASE)
  so `name[expr]` indexing is no longer read as `[...]` generics.
- Sibling bug `parser_array_index_misread_as_generics_2026-06-14.md` (same
  defect: `matched[j]` flagged with this exact suggestion) was closed
  2026-09-13 as fixed, verified by execution.

**Re-verification 2026-11-25** (pinned `bin/simple.exe`, Simple v1.0.0-rc.1,
build-commit `1343b77bbaa`, worktree on `release/1.0.0`):

- Lint half — no longer reproduces. A minimal file with
  `if next_depth[cpu] > 0:` lints clean of any angle-bracket suggestion:
  `SIMPLE_LIB=src bin/simple.exe lint /tmp/repro.spl` emits only
  `warning[PANIC-W-INDEX]` with a valid hint (`next_depth.get(cpu) ?? <default>`).
  The original `src/os/kernel/scheduler/green_carrier.spl` likewise lints
  with zero "angle" warnings (only `PANIC-W-INDEX`/`MODINIT001`).
- Parse half — behaves exactly as documented, and correctly so:
  `if next_depth<cpu> > 0:` fails with
  `parse: ... Unexpected token: expected expression, found Gt at line 4, column 24`
  (JIT and interpreter fallback agree). The suggested form was never valid
  index syntax.
- The bracket form runs: the same program with `next_depth[cpu]` exits 20
  (= `next_depth[1]`).
- Rule spec: `SIMPLE_LIB=src bin/simple.exe test
  test/01_unit/compiler/parser/lt_then_bracket_index_repro_spec.spl` —
  2 passed, 0 failed.

**Outcome:** no source change required. The mismatch was lint-side,
Rust-seed-only, and the seed fix is already in the tree; the pure-Simple
compiler neither emits the bad suggestion nor accepts the invalid syntax.
Closing.
