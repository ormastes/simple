# Hosted-WM entry closure was unparseable: two grammar gaps + three landed syntax errors

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).
CLOSED in the grammar** — see "Update 2026-08-01" at the end. Gap B
(multi-line `match` as a struct-literal field value) is tracked separately.
**Found:** while trying to calibrate `GLYPH_RGB_SHA256` for
`scripts/check/check-linux-hosted-wm-live-window-evidence.shs` (showcase
cells 4/5/6).
**Base revision:** `f7bfaf973de2a2c398fec7f11ea4235e19f557ab` (origin/main).

## Headline

At origin/main, `src/os/hosted/hosted_entry.spl`'s entry closure **did not
parse with any Simple compiler** — not the pure-Simple `native-build`
front end and not the Rust seed. Three source sites were syntactically
invalid, so the hosted-WM artifact could not be produced at all. Every
`check-linux-hosted-wm-live-window-evidence.shs` outcome downstream of the
build — including the pending glyph oracle — was therefore unreachable.

This is upstream of, and independent from, the `GLYPH_RGB_SHA256=pending`
placeholder. Fixing the placeholder alone would not have made cells 4/5/6
passable.

## Gap A — assignment-statement RHS rejects newline continuation

`val`/`var` declarations accept a newline after `=`; a plain assignment
statement does not. Rejected identically by the seed and by the
pure-Simple front end.

| Form | Result |
|---|---|
| `val a =` ⏎ `    40 + 2` | PARSES |
| `c =` ⏎ `    a + 1` | **FAILS** — `expected expression, found Newline` |
| `self.f =` ⏎ `    x.y` | **FAILS** — same |

Repro (both engines):

```
fn main():
    val a =
        40 + 2
    var c: i64 = 0
    c =
        a + 1
    print("a={a} c={c}")
```

Landed instance: `src/os/hosted/hosted_browser_renderer_worker.spl:1098`
(`self.input_view_start_byte =` with the RHS on the next line).

## Gap B — multi-line `match` is not accepted as a struct-literal field value

A multi-line `if`/`elif`/`else` **is** accepted as a named field value in a
struct literal; a multi-line `match` in exactly the same position is not.
The parser tries to read the trailing `,` as another match-arm pattern.

| Form | Result |
|---|---|
| `a: if cond:` ⏎ `    "y"` ⏎ `else:` ⏎ `    "n",` | PARSES |
| `a: match opt:` ⏎ `    Some(r): f(r)` ⏎ `    nil: "",` | **FAILS** — `expected pattern, found Comma` |

Repro (both engines):

```
struct Out:
    a: text
    b: i64

fn main():
    val active: text? = Some("x")
    val o = Out(
        a: match active:
            Some(r): r
            nil: "",
        b: 7
    )
```

Landed instances: `src/os/hosted/hosted_web_content_session.spl` at the
`semantic_target_id:` field of three `HostedWebContentDispatch(...)`
literals.

## Gap C — `elif` trailing-operator continuation (already filed, still open)

`src/lib/gc_async_mut/web/browser_session_runtime.spl:2160` used

```
            elif event_type == "click" and
                 dispatch.default_action == "form-reset":
```

which fails with `expected expression, found Indent`. This is exactly the
`elif` sub-case left open by
`doc/08_tracking/bug/if_condition_operator_line_continuation_parse_2026-07-30.md`
("Remaining gap"). Confirmed still open on 2026-08-01. Every other one of
the 15 `elif`-with-trailing-operator sites in `src/os` + `src/lib` already
carries the parenthesised workaround; this one did not. Repaired here by
parenthesising, matching its 14 siblings.

## What this change does

Repairs the four landed sites only — assignment joined onto one line, and
the `match` expressions hoisted to a preceding `val`. Semantics unchanged.

**The repairs are workarounds, recorded here deliberately rather than
normalized silently** (per `CLAUDE.md`: a short, safe grammar form that
fails must be fixed or filed). Both gaps remain open in the grammar.

## Why it went unnoticed

`bin/simple lint` does not catch syntax errors
(`doc/08_tracking/bug/../reference` — lint is fail-open on parse), and no
spec compiles `src/os/hosted/**`, so invalid syntax can land and stay
landed. A parse-only sweep over `src/os` + `src/lib` is the cheap guard:
`simple_seed compile <file> -o /dev/null` is ~0.5s/file.

## Fix direction

- Gap A: allow the assignment-statement RHS to take the same
  newline-continuation path the `val`/`var` initializer already takes.
- Gap B: when parsing a `match` used as an expression inside a
  bracketed/parenthesized argument or field list, terminate the arm list at
  a `,` that belongs to the enclosing list rather than demanding another
  pattern.

## Update 2026-08-01 — Gap A and Gap C are CLOSED (PROVED)

Both were fixed in the seed parser shortly after this doc was written, and
are re-verified closed at origin `b9341804e5`:

| Gap | Shape | Fix | State at `b9341804e5` |
|---|---|---|---|
| A | `c =` ⏎ `a + 1`, `self.f =` ⏎ `x.y`, and every compound assign | `6587c9e8875` — `parse_expression_or_assignment` skips newlines/indents after the assign-op, with a deferred-dedent drain | **PARSES** |
| C | `elif a and` ⏎ `b:` (and `==`, `>`, `or`, `else if`, chained `elif`, deep and shallow indent shapes) | `a7e5fbccf85` + the shared `parse_condition_block` drain in `parser_impl/core.rs` | **PARSES** |

Evidence: a probe test built against the tip `simple-parser` crate parses
all of the shapes above, including the exact real-world dispatch condition
from `src/lib/gc_async_mut/web/browser_session_runtime.spl:2160`, while a
deliberate syntax-error fixture in the same run still fails. The full
`cargo test -p simple-parser` suite is green at that tip (0 failed).

**Why this doc read as open longer than it was:** the deployed
`bin/simple_seed` in this workspace is a **2026-07-25** binary — older than
both fixes. Compiling the repro with it reproduces the original error
strings verbatim (`expected expression, found Newline` for Gap A,
`expected expression, found Indent` for Gap C), which is indistinguishable
from the grammar still being broken. Any future check of a parser gap must
probe the tip source (`cargo test -p simple-parser`) or a freshly built
binary, never `bin/simple_seed` or `bin/simple` as deployed.

**Consequence for the workarounds.** The paren workaround at
`browser_session_runtime.spl:2160` and its 14 siblings, and the joined-onto-
one-line assignment repairs listed above, are no longer required by the
grammar. They are deliberately **not** unwound here: the deployed toolchain
still predates the fixes, so removing them would make those files
unparseable for anyone building with the currently deployed binary. Unwind
them in the same change that redeploys a binary built at or after
`6587c9e8875` + `a7e5fbccf85`.

**Language-level regression coverage added:**
`test/01_unit/compiler/parser_line_continuation_assign_elif_spec.spl` pins
both shapes in Simple itself rather than only in Rust unit tests — the file
is written in the shapes it pins, so a regression stops it loading.
Non-vacuity, same command on the same file, two binaries:

- pre-fix (2026-07-25) `simple_seed`: `FAIL ... parse: Unexpected token:
  expected expression, found Newline` — `Results: 1 total, 0 passed, 1
  failed`. A known-good control fixture compiles in the same run.
- binary built from tip: `PASS` — `Results: 13 total, 13 passed, 0 failed`.

The 13 assertions check evaluated *results*, not merely that the file
loads, so a silent mis-association of a continued condition or RHS fails
the spec rather than passing it.
