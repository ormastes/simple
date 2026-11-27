# Stage 2 multiline `if` continuation divergence

Date: 2026-08-14
Status: FIXED (2026-11-11, lane boot17; originally RESOLVED 2026-08-17) —
self-hosted lexer glues the leading-`and` continuation; regression spec
`test/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.spl`
re-verified 4/4 on the fresh seed. See addendum.
Owner: compiler frontend

The freshly rebuilt bootstrap seed accepts the parenthesized multiline
condition in
`src/compiler/60.mir_opt/mir_opt/typed_storage_view_producer.spl`, while the
Stage 2 self-host parser rejected the unparenthesized equivalent at the newline
before `and` with `expected :, got Newline`.  The compact form is intended to
remain valid language syntax; bootstrap recovery uses explicit grouping until
the Stage 2 parser's continuation handling is brought into parity.

Reproducer:

```text
if first
    and second:
    return true
```

Expected: the continued boolean condition parses identically across seed and
self-hosted stages.  Actual: Stage 2 terminates the condition after `first`.

Regression gate needed: parse the reproducer through both the core/bootstrap
parser and the deployed self-hosted parser, then remove the explicit grouping
workaround only after both accept it.


## 2026-08-17 re-verification — half the gate can be closed now

The "regression gate needed" above asks for the reproducer to be parsed by BOTH
the core/bootstrap parser and the deployed self-hosted parser. The first leg is
now measured; the second is blocked on this host.

**Seed/bootstrap parser: ACCEPTS the unparenthesized form.** Direct `bin/simple
run` of the exact reproducer shape:

```
fn probe(first: bool, second: bool) -> bool:
    if first
        and second:
        return true
    false
```

prints `unparen=true` — it parses, and evaluates correctly. So the compact form
is valid language syntax as the seed implements it, confirming the doc's stated
intent rather than contradicting it.

**Self-hosted Stage 2 parser: NOT MEASURED — blocked.** The divergence is by
definition in `src/compiler/**`'s parser as executed by a Stage 2 binary. No
Stage 2/3 binary is present on this host, and producing one requires a full
bootstrap, which this lane is explicitly forbidden from running. The claim
"Stage 2 terminates the condition after `first`" therefore remains an
unreproduced historical observation here.

**Precise remaining blocker:** an admitted Stage 2 (or Stage 3) pure-Simple
binary. Given one, the whole gate is: feed the snippet above to it and assert it
does not report `expected :, got Newline`. Only then may the explicit-grouping
workaround in
`src/compiler/60.mir_opt/mir_opt/typed_storage_view_producer.spl` be removed.

Not spec-testable from this lane: an SSpec example runs under whichever binary
invokes it, so a spec written here would exercise the seed parser (already
green) and would silently prove nothing about the Stage 2 parser that is
actually under suspicion. Writing one would manufacture a false green, so none
was added.

## RESOLVED 2026-08-17 — fixed in current source; the report was seed staleness

The self-hosted lexer at tip GLUES the continuation. Driving
`core.lexer.lex_init`/`lex_next` (i.e. `src/compiler/10.frontend/core/
lexer_struct.spl`) over the reproducer emits NO `Newline` token between the
condition operand and the leading `and`:

```
... 40(if) 6 80(==) 1 55(and) 6 80 1 161(:) 180 181 ...
```

`CoreLexer.leading_op_continues` (`lexer_struct.spl:325`) plus
`line_starts_binary_op`'s word-operator arms (`:303-306`) implement it, with
guard 1 `token_can_end_expr` and guard 2 strictly-deeper-indent as the two
negative controls. `typed_storage_view_producer.spl:98-99` already carries the
unparenthesized form; no workaround remains to remove.

Regression spec (drives the SELF-HOSTED lexer, which the pre-existing
`test/01_unit/compiler/parser_leading_operator_continuation_spec.spl` cannot,
since a spec's own source is lexed by the Rust seed that executes it):
`test/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.spl`

```
Results: 4 total, 4 passed, 0 failed
SPEC FILE VERDICT: ... declared>=4 executed=4 passed=4 failed=0 dropped=0
```

## Addendum 2026-11-11 (lane boot17) — FIXED, re-verified on the fresh seed

**Verification actually run** (worktree simple-p3-boot17-20261111, branch
`work/p3-boot17-20261111`, fresh seed 46fe8f6b6def):

```
SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe test \
  test/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.spl \
  --mode=interpreter --no-cache
# SPEC FILE VERDICT: ... outcome=OK declared>=4 executed=4 passed=4 failed=0
```

The earlier "self-host leg BLOCKED" qualifier in this doc's status line is
resolved by the 2026-08-17 RESOLVED analysis and remains true at this source:
the regression spec drives the SELF-HOSTED lexer (`core.lexer.lex_init` /
`lex_next`, `src/compiler/10.frontend/core/lexer_struct.spl`) in-process, so
it exercises the Simple-source lexer's continuation handling — not the Rust
seed's lexing of the spec file — and no Stage-2 binary is needed for that leg.
The unparenthesized form is live in the compiler source the spec protects:
`src/compiler/60.mir_opt/mir_opt/typed_storage_view_producer.spl:68`
(`and declaration.base_local_id == base_local_id:`). No explicit-grouping
workaround remains to remove.
