# Hosted-WM entry closure was unparseable: two grammar gaps + three landed syntax errors

**Status:** source repaired (this change); **both grammar gaps still OPEN.**
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
