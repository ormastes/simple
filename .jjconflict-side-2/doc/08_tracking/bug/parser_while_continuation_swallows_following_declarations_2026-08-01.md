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
3. ~~`parse_condition_block`'s flat-body path parses only ONE statement, so an
   `if` with a multi-statement equal-column body silently drops the rest. Same
   family of silence, separate mechanism — needs its own reproducer.~~
   **FIXED — see "Follow-up 3 resolved" below.** The filed guess that it was
   *silent* turned out to be wrong for the equal-column shape; it is a hard
   parse error. The silent variant is a different shape. Both are characterised
   below.
4. `test-runner: no examples executed` should name the module and say whether it
   loaded, rather than being the sole symptom of a load failure.

## Follow-up 3 resolved — `if`/`elif` equal-column continuation (2026-08-01)

### Correction to the filed guess (PROVED)

Follow-up 3 predicted a *silent* drop. Measured on the pristine tree at
`a6b56173fda`, the equal-column `if` shape is **not** silent — it is a **hard
parse error**, typically `expected "expression", found "Dedent"` or
`expected "Indent", found "Var"`, reported at a line well past the real fault.
Valid code is rejected; nothing is silently dropped. The correction matters
because "silent" and "loud but mislocated" call for different verification.

There IS a silent shape in the same function, but it is a different one — see
"The other flat body" below.

### Minimal reproducer (PROVED, pristine `a6b56173fda`)

```
fn f(n: i64) -> i64:
    if n
        > 0:
        var a = 1
        var b = 2
        return a + b
    return 0
```

Pristine: `ERR UnexpectedToken { expected: "expression", found: "Dedent",
line: 8, column: 1 }` — the fault is the `if` on line 2, the error points at
EOF. The single-line control (`if n > 0:`) parses to 1 top-level item with a
3-statement `then` block. Reducing the body to ONE statement makes the repro
parse correctly, which is the tell: the limit is the statement count, not the
grammar of the continuation.

### Root cause (PROVED)

`parse_condition_block` (`parser_impl/core.rs`) delegated to
`parse_block_after_newline`. That function's documented "flat body" path
(`if cond:` with the body on the next line at the SAME column as the `if`)
deliberately parses exactly **one** statement via `parse_item`.

In the equal-column continuation shape the lexer emits **no fresh `Indent`** for
the body — the continuation line's pseudo-INDENT already opened the block — so a
genuinely indented multi-statement body is indistinguishable, at that one token,
from a flat body. `parse_condition_block` took the flat path, kept statement 1,
let statements 2..n leak to the enclosing block, and then still owed a deferred
DEDENT that had in fact already been spent. The desynchronisation surfaces later
as the mislocated error.

`while`/`for`/`match` do not reach this: their header parsers detect the shape
themselves (`header_continuation_is_equal_column`) and call `parse_block_body`,
which loops until `Dedent`. `if`/`elif` reach their block through
`parse_condition_block`, which did not — so the earlier fix did not cover them.

### Fix

`parse_condition_block` now uses the same two shared helpers as the loop headers:
when `header_continuation_is_equal_column(deferred_before)` holds it calls
`parse_block_body()` directly (multi-statement, terminates on `Dedent`) instead
of `parse_block_after_newline()`, and reconciles the deferred count through
`header_continuation_dedents_to_reconcile(deferred_before, equal_column)`. One
site, +28/-3 lines in `parser/src/parser_impl/core.rs`; no lexer change.

### The family (PROVED by probe, pristine vs fixed)

Fixed by this change (pristine = parse error, fixed = identical tree to the
single-line control):

- `if` equal-column continuation, multi-statement body — in a function, nested
  inside another `if`, and at module top level
- `elif` equal-column continuation, including two `elif`s in one chain
- `else if` equal-column continuation
- `if` equal-column continuation followed by `elif`/`else` branches
- **match-arm guards** (`case x if x\n    > 0:`) — they reach the same funnel
  through `parse_inline_or_block`, and were broken pristine

Already correct, unchanged by this change (verified both states):

- the **deep** continuation shape (continuation column deeper than the body) —
  covered by `drain_available_deferred_dedents`
- `else:` bodies of any length — no condition, so no continuation, so
  `deferred_before` is 0 and the equal-column branch is never taken
- a **single-statement** equal-column body — the one case the flat path got right
- `while`/`for`/`match` equal-column bodies — fixed earlier in this document

### The other flat body — genuinely silent, deliberately NOT changed

```
fn f(n: i64) -> i64:
    if n > 0:
    var a = 1
    var b = 2
    return a + b
```

Body at the `if`'s OWN column, no header continuation. This parses `Ok` on both
trees, the `if` gets **one** statement, and `var b` / `return` are silently
re-parented into the enclosing function — they now run unconditionally. That is
the documented flat-body rule (`parse_block_after_newline`'s comment gives
exactly this shape), and making it greedy would swallow the remainder of the
enclosing block, i.e. trade one silent mis-parenting for a worse one. The fix
here is gated on `deferred_before > 0`, so this shape is untouched; the gate test
pins it with `true_flat_body_stays_single_statement` so a future change to it is
a deliberate act.

Two open questions recorded rather than answered: (a) whether this shape should
be a parse error instead of a silent re-parent, and (b) that `while`/`for` reject
it outright (`expected "Indent", found "Var"`) while `if` accepts it — an
inconsistency between the loop and condition families.

### Evidence (this change)

Pristine and fixed binaries built from the **same tree and same profile**
(`cargo test -p simple-parser`, `test` profile) — the only delta is
`parser/src/parser_impl/core.rs`.

Gate: `parser/tests/if_condition_block_equal_column_gate.rs`, 10 tests. Pristine
**6 fail / 4 pass**; fixed **10 pass**. Comparison is a **span-free structural
digest** of the whole statement tree, not a top-level item count, so it detects a
statement moving between blocks inside a function. The 4 that pass pristine are
the deliberate controls: the loop family, the single-statement body, the
true-flat-body guard, and a non-vacuity assertion that every repro fixture
differs from its control.

Full `simple-parser` suite, `--no-fail-fast`, both states:
pristine **44 test binaries / 936 passed / 0 failed**, fixed **45 / 946 / 0**
(+1 binary, +10 tests = the new gate exactly).

Corpus A/B over **12,883** `.spl` files under `src/lib`, `src/app` and
`src/compiler` (a superset of the 9,769 used above), run under both binaries:

- `parser/tests/corpus_item_count_dump.rs` — 12,882 data lines,
  **byte-identical**, same 43 pre-existing parse failures
- a deeper scratch harness emitting a **full nested structural digest per file**
  (fn/if/elif/else/while/for/loop/match-arm/class-method block sizes) — also
  **byte-identical**. This is strictly stronger than the item count: it would
  catch a statement moving between blocks *inside* a function, which the item
  count cannot.

Blast radius on real code is zero.

No `.spl` spec is added, for the same reason as above: the pure-Simple parser
still rejects the leading-operator form outright (follow-up 1). **Condition for
adding one:** when follow-up 1 lands and the pure-Simple parser accepts the
leading-operator continuation, add a spec covering the `if`/`elif`/`else if`/
match-arm-guard equal-column shapes and delete this note.
