# A multi-line loop/match HEADER silently swallows every following declaration

**Date:** 2026-08-01
**Status:** FIXED (parser + run-path diagnostic), gates landed
**Severity:** CRITICAL — the module produced NO output and exit code 0. Not a
wrong value, not a parse error: nothing at all.
**Found by:** widening
`doc/08_tracking/bug/parser_leading_operator_line_continuation_2026-08-01.md`
(section "NEW DEFECT found while widening: `while`-condition continuation")
**Base:** origin `5ca84bcefe5f3cd65d89e94723bca0308cd9f97f`

## Symptom (PROVED, deterministic)

```
$ simple m/d2.spl
$ echo $?
0
```

Zero bytes of output. No parse error, no location, no symbol name, no non-zero
exit. `simple compile m/d2.spl -o out.smf` was worse: it printed
`Compiled m/d2.spl -> out.smf` and exited 0, producing an SMF from a module
whose `main` had vanished.

The originally-reported form was a spec that reported only
`error: test-runner: no examples executed`.

## Minimal reproducer (PROVED)

The original report said two declarations were required and named "if/else arms
beginning with a unary minus" as the second ingredient. **Both claims are
wrong.** ONE declaration suffices and the unary minus is irrelevant:

```simple
fn w(n: i64) -> i64:
    var i = 0
    while i
        < n:
        i = i + 1
    if n > 0:
        return 1
    else:
        return 2

fn main():
    print("A")
    print("B")
```

The actual ingredients are:

1. a loop/match **header** whose expression uses a leading-operator line
   continuation, **whose continuation line sits at the same column as the block
   body** (the equal-column shape), and
2. anywhere later in the same enclosing block, an `if … else` whose arms open
   their own INDENT, and
3. at least one declaration after that — which is what gets eaten.

Unary minus is a red herring: `if c: 1 else: 2` reproduces identically.
Order matters — putting the `while` function AFTER the `if/else` function parses
fine, because nothing follows it.

Ruled out by control (all parse and run correctly):

| variant | result |
|---|---|
| single-line `while i < n:` | OK |
| `if` (not `while`) with the same continuation | OK |
| `if` with no `else` | OK |
| `if/else` whose arms are assignments, followed by a statement | OK |
| the while-continuation function with nothing after it | OK |

## Root cause (PROVED)

`src/compiler_rust/parser/src/stmt_parsing/control_flow.rs`, in the four loop /
match header parsers (`parse_while_with_label`, `parse_for_with_label`, and the
two `match` subject sites).

A leading-operator continuation consumes a pseudo-INDENT
(`binary_indent_count`), whose matching DEDENT is deferred into
`deferred_dedent_count`. Each header parser then handles the **equal-column**
shape specially: when the continuation line's column equals the block body's
column the lexer emits no fresh `Indent` at all, so the parser skips
`expect(Indent)`.

But in exactly that shape the pseudo-INDENT **is** the block's own INDENT, so
`parse_block_body` already consumes its matching DEDENT as the body terminator.
The code nevertheless ran

```rust
let deferred = self.deferred_dedent_count + deferred_before;
self.deferred_dedent_count = 0;
self.consume_dedents_for_method_chain(deferred);
```

counting that same DEDENT a second time. The surplus re-defers, rides through
the following `if`/`else` blocks, and is finally spent on the DEDENT that closes
the **enclosing function body**. From that point the parser believes it is still
inside `fn w`, so every following top-level declaration is re-parented as a
nested item.

`Parser::parse()` still returns `Ok`. There is no error to report, which is why
nothing anywhere reported one.

Confirmed directly: with `fn main` placed FIRST (so it survives) and `later()`
declared after the `if/else`, the run fails with
`error[E1002]: function 'later' not found` — the declaration is gone from module
scope while `w` itself still evaluates correctly.

**`par_had_error_mirror` is not involved.** That is the pure-Simple parser's
error-mirror channel; this path is the Rust seed parser and it never records an
error at all. (The pure-Simple parser rejects the same file loudly but
uselessly: `lint` reports `m/c6.spl:1:0: error[PARSE001]: Source did not parse`
— an error with no real location. Tracked separately.)

## Why it was silent — the second, larger defect

Even with a correct parser this class stays invisible, so the silence was fixed
independently of the grammar.

`src/compiler_rust/driver/src/exec_core.rs` had THREE no-`main` fallbacks
(`run_source_in_memory_native`, `run_file_jit`, `run_file_interpreted_with_args`)
that each called `evaluate_module(&items)` and returned its exit code. For a
module consisting only of declarations that evaluates nothing and returns 0 —
so "your `main` disappeared" and "ran successfully" were the same observable.

This is also the documented verification trap that a file with no `fn main`
"exits 0 without parsing", which has previously voided negative-control runs.

Fix: `reject_silent_no_op_module` rejects a run whose module has no top-level
`main` **and** no executable top-level item, and says so:

```
error: no `main` function and no top-level statements: this module declares only
names, so running it would execute nothing
  = note: a `main` was found NESTED inside another function's body. That is
    almost always an indentation/line-continuation mis-parse that re-parented the
    following declarations — check any multi-line `while`/`for`/`match` header
    just above it.
  = help: add `fn main():`, or run this file with `simple test` / import it
    instead of running it directly
```

The predicate is written as "every item is a *known* pure declaration", so a
newly added `Node` variant defaults to executable and can never produce a
spurious error.

## The family (all four sites fixed)

The same double-count existed at every header that reconciles a
continuation pseudo-INDENT against a block body it did not open:

| site | construct |
|---|---|
| `control_flow.rs` `parse_for_with_label` | `for x in <continuation>:` |
| `control_flow.rs` `parse_while_with_label` | `while <continuation>:` |
| `control_flow.rs` match subject (statement form) | `match <continuation>:` |
| `control_flow.rs` match subject (expression form) | `match <continuation>:` |

`parse_condition_block` (`if`/`elif`/`else`) is NOT affected: its flat-body path
does not consume the DEDENT, so reconciling afterwards is correct there.

## Fix

- `parser/src/parser_helpers.rs`: new `header_continuation_is_equal_column` and
  `header_continuation_dedents_to_reconcile`; the latter drops one deferred
  DEDENT in the equal-column shape (`saturating_sub(1)`), because the block body
  already consumed it.
- `parser/src/stmt_parsing/control_flow.rs`: all four sites now capture
  `equal_column` and reconcile through the shared helper.
- `driver/src/exec_core.rs`: `reject_silent_no_op_module` wired into all three
  no-`main` fallbacks.

## Evidence

Both binaries built from the SAME tree and profile; the only difference is the
patch, so the delta is attributable to the fix and not to source drift.

| fixture | pristine `5ca84bce` | fixed |
|---|---|---|
| `c6` / `c5` / `c1` / `d2` / `e1` (repro shapes) | **rc=0, ZERO output** | correct output, rc=0 |
| `f1` (calls a swallowed `later()`) | rc=1 `function 'later' not found` | `start` / `42` |
| `nomain.spl` (declarations only) | **rc=0, ZERO output** | rc=1, loud located error |
| `good.spl` (control) | `ok` | `ok` |
| `bad.spl` (deliberate syntax error, control) | rc=1, reported | rc=1, reported |

Gate: `parser/tests/header_continuation_swallow_gate.rs` — 4 of 5 tests FAIL on
pristine (`while <`, `while and`, `for +`, `match +`; each `Some(1)` vs control
`Some(3)`) and all 5 pass after. The 5th asserts the repro and control fixtures
actually differ, so the suite cannot pass vacuously.

Full `simple-parser` suite: 43 test binaries, 0 failures, before and after.

Corpus regression: `parser/tests/corpus_item_count_dump.rs` (an `#[ignore]`d A/B
harness) parsed all **9,769** `.spl` files under `src/lib` and `src/app` on both
trees. The two dumps are **byte-identical** — same top-level item count per file,
same 43 pre-existing parse failures. Blast radius on real code is zero.

No `.spl` regression spec is added here on purpose. The pure-Simple parser still
rejects the leading-operator form outright (follow-up 1 below), so a spec
covering these shapes would go RED for an unrelated reason on the default
tooling. The gate lives at the Rust parser level, where the defect is, until
follow-up 1 lands — then the spec should be added and this note removed.

## Follow-ups (not fixed here)

1. The pure-Simple parser rejects these files with
   `error[PARSE001]: Source did not parse` at `1:0` — loud but with no usable
   location. It needs the real span.
2. `simple compile <file>` reports success for a module whose `main` was
   swallowed. The no-op guard covers the RUN paths; the COMPILE path should
   grow an equivalent check.
3. `parse_condition_block`'s flat-body path parses only ONE statement, so an
   `if` with a multi-statement equal-column body silently drops the rest. Same
   family of silence, separate mechanism — needs its own reproducer.
4. `test-runner: no examples executed` should name the module and say whether it
   loaded, rather than being the sole symptom of a load failure.
