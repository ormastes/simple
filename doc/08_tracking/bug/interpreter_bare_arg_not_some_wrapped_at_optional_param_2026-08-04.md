# Interpreter does not Some-wrap a bare argument at a `T?` parameter — `case Some(x)` matches nothing and the whole `match` falls through

- **Filed:** 2026-08-04
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
  `src/compiler_rust/compiler/src/interpreter_patterns.rs` (the `Pattern::Enum`
  arm), **not** where this report predicted. See "Correction" below.
- **Severity:** high — silent wrong behaviour, and a corpus-wide false-green generator
- **Engines:** interpreter only. The JIT was already correct.
- **Blast radius:** 1,762 `case Some(` sites across 423 `.spl` files under `src/`.

## Correction 2026-08-05 — the title and the diagnosis were both wrong

**There is no missing Some-wrap, and there is no coercion site to fix.**
Re-measured on one binary, `SIMPLE_EXECUTION_MODE` the only variable:

- **Neither engine wraps.** A bare `T` bound to a `T?` is stored as the RAW
  value under the JIT too. `fn show(v: i64?) -> text: "{v}"` called as
  `show(42)` prints a raw i64 under the JIT, not `Option::Some(42)`; and
  `match v: case 42:` **takes the literal arm** under the JIT, which it could
  not do if the value were wrapped. `val v: i64? = 42` — a local, no parameter
  passing involved — reproduced the identical fall-through, which a
  parameter-binding defect cannot explain.
- **The divergence was in the PATTERN, not the coercion.** The JIT's `Some(p)`
  arm matches any non-nil, non-enum value and binds `p` to the value itself. The
  interpreter's `Pattern::Enum` arm fell through to `Ok(false)` instead.
- **The JIT's binding was never "corrupt".** An earlier reading in the source
  comment claimed `i64 6` binds `<value:0x6>` and `[10,20,30].first()` binds a
  denormal float. Re-measured by VALUE rather than by `to_text` — `x == 42`,
  `x == "hi"`, `x == true`, `x == 2.5`, `x.len()`, `x.field` — the JIT binding
  is CORRECT for i64, text, bool, f64, array and class instances. The hex and
  denormal renderings are artifacts of `to_text` over an untagged raw value, a
  separate and still-open defect.
- **The pure-Simple interpreter was already right**, and independently confirms
  the chosen semantics: `src/compiler/10.frontend/core/interpreter/eval.spl:928-937`
  matches flat `Some` by binding the raw word, returns `false` for `Ok`/`Err`
  on the same shape, and treats nil as `None`. The Rust seed is now aligned to
  it and to the JIT — no third behaviour was invented.

Scope of the fix is `Some` with payload sub-patterns only. `case Ok(x)` /
`case Err(e)` over a bare value do **not** match under the JIT either
(measured), and `case Some:` without payload already matched in both engines.

## Blast radius, measured before landing

Turning on 1,762 previously-dead arms executes code that has never run, so the
fallout was measured rather than assumed. Two binaries built from the same
worktree, differing only in this fix; 534 candidate specs each, run the way the
test runner runs them (`SIMPLE_RUNTIME_MODE=interpreter
SIMPLE_EXECUTION_MODE=interpret`), scored on the authoritative
`SPEC FILE VERDICT:` line with ANSI stripped — never `tail -1`.

Candidate set = every spec that either contains `case Some(` itself (139) or
names one of the 423 `src/` files carrying `case Some(` (410), unioned to 534.

```
baseline rows: 534   fixed rows: 534
NOVERDICT:      19          19      (identical file set — no new crashes/timeouts)
failing files: 138         138
example COUNT changed:       0      (no spec gained or dropped an example)
newly failing:               3
newly passing:               7
```

**Newly passing — 7 files, 20 examples.** Includes
`test/01_unit/language/dict_get_option_match_spec.spl` (3 → 0), which is the
spec written directly against this semantics and which asserts BOTH directions.
Baseline reported `expected -1 to equal 42` and `expected 0 to equal 7`; those
now bind the real payloads, while its "does not take the Some arm for an absent
key" and "takes the None arm for an absent key" examples pass on **both**
binaries — so `Some` did not become irrefutable. Also
`style_block_resolve_selectors_spec.spl` (2 → 0),
`naked_struct_pattern_match_arm_spec.spl` (1 → 0),
`resolve_nil_guard_spec.spl` (5 → 4),
`vhdl_hardware_call_lowering_contract_spec.spl` (6 → 3), and
`url_utils_spec.spl` (27 → 23, counted twice — `test/01_unit/` and `test/`
are duplicate trees).

**Newly failing — 3 files, 14 examples, ONE cause, and it is not the engine.**
`chart_gui_view_spec.spl`, `sheet_gui_session_spec.spl` and
`sheet_gui_view_spec.spl` each defined a local

```
fn _dump_contains(haystack: text, needle: text) -> bool:
    val idx = haystack.index_of(needle)
    match idx:
        case Some(_): return true
        case _: return false
```

citing "index_of's Option". **`index_of` returns a plain i64 with `-1` for not
found — measured identically under the interpreter, the JIT and the pure-Simple
engine. There is no Option.** So under the defect this helper returned `false`
for *every* input, and each `assert_false(_dump_contains(...))` was **vacuously
green: it could not have failed**. The fix inverts it to `true` for every input,
which is what made the vacuity visible.

The repo's own production code already had this right —
`src/app/ui.render/_TuiWidgets/extended_widgets.spl:119-123` carries the comment
*"index_of returns a plain i64 (-1 == not found), not an Option"* and uses
`>= 0`. The three helpers were corrected to that form (not suppressed, and no
assertion was weakened); all three files then verify 15/15, 31/31 and 9/9 with
`failed=0 dropped=0`. Independently confirmed against production behaviour: the
rendered sheet dump is byte-identical on both binaries (`3|7`, no formula text),
so no product code changed answers here.

**Net: the fix turns 20 examples green, and the only examples it turns red were
assertions that could never have failed in the first place.** No product spec
regressed.

## Summary (as originally filed — see the correction above)

When a function declares `p: T?` and the caller passes a **bare `T`** (not an
explicit `Some(...)`), the interpreter binds the raw value rather than wrapping
it in `Some`. A subsequent `match p:` with `case Some(n)` / `case None` then
matches **neither arm**. There is no error and no default arm: execution simply
continues past the `match` into whatever statement follows.

`nil` is handled correctly — `case None` matches in both engines. Only the
present-value arm is affected.

The JIT wraps correctly, so the defect is invisible in a plain `simple run`
of a file that JIT-compiles. `src/app/test_runner_new/test_runner_single.spl`
forces `SIMPLE_RUNTIME_MODE=interpreter` and `SIMPLE_EXECUTION_MODE=interpret`
for every spec child, so **every spec in this repo runs on the broken path**.
No spec can currently observe a `case Some(x)` arm on a `T?` parameter that
received a bare value.

## Minimal repro

`test/fixtures/optional_arg_coercion/opt_min_main.spl` (committed with this report):

```
class Box:
    val tag: text

fn m_box(p: Box?) -> text:
    match p:
        case Some(n):
            return "Some:" + n.tag
        case None:
            return "None"
    "FELL_THROUGH"
```

with `m_box(Box(tag: "x"))`, `m_box(nil)`, and the same shape for `i64?` and
`text?`. One binary, one file, one variable — the execution mode:

```
$ simple run test/fixtures/optional_arg_coercion/opt_min_main.spl
MAIN_box=Some:x
MAIN_box_nil=None
MAIN_int=Some:7
MAIN_text=Some:hi

$ SIMPLE_RUNTIME_MODE=interpreter SIMPLE_EXECUTION_MODE=interpret \
    simple run test/fixtures/optional_arg_coercion/opt_min_main.spl
MAIN_box=FELL_THROUGH
MAIN_box_nil=None
MAIN_int=FELL_THROUGH
MAIN_text=FELL_THROUGH
```

The `FELL_THROUGH` string is the statement *after* the `match`. It is reached
because no arm was taken — not because a `None` arm returned it.

It is not a closure defect, though it looks like one at first: adding any
lambda to the file makes the driver refuse to JIT (`the JIT closure ABI does
not tag-box lambda arguments or results`) and fall back to the interpreter, at
which point even a call from `fn main` starts returning `FELL_THROUGH`. The
axis is the engine, not the call site.

## Observed production consequence

`src/lib/gc_async_mut/gpu/browser_engine/style_block_resolve.spl`,
`selector_matches`, lines 39-43:

```
        match parent:
            case Some(parent_node):
                return simple_selector_matches(parent_selector, parent_node, 1, 1)
            case None:
                return false
```

Under the interpreter neither arm runs, so control reaches the *descendant*
combinator branch below and the function returns `true` from the
"any-ancestor" path. A strict child combinator therefore degrades into
descendant-like matching — precisely the failure the code's own comment says it
exists to prevent ("keep this strict instead of letting whitespace tokenization
degrade it into descendant-like matching").

Demonstration, same binary, same file:

```
selector_matches("p > span", <span>, <div parent>, 1, 1)
  fn main        -> false   (correct: the parent is a div, not a p)
  spec `it` body -> true    (wrong)
```

`test/fixtures/optional_arg_coercion/selector_child_combinator_main.spl`
reproduces it on one binary by switching only the execution mode:
`parent_mismatch=false` under the JIT, `parent_mismatch=true` under the
interpreter, with `no_parent` (the `case None` arm) correct in both.

## Coverage consequence — RESOLVED

Line 41 of `style_block_resolve.spl` (`return
simple_selector_matches(parent_selector, parent_node, 1, 1)`) was **not
coverable by any spec** while this defect stood, and was excluded from the
"reachable" denominator in `style_block_resolve_selectors_spec.spl` on that
basis. It is now covered: three examples were added to the
`style_block_resolve child combinator` describe, including a by-value pair on
the same node and parent where `div > span` must answer false and `div span`
must answer true. Measured on one spec file, one binary each:

```
baseline  SPEC FILE VERDICT: ...style_block_resolve_selectors_spec.spl declared>=29 executed=29 passed=27 failed=2 dropped=0
            ✗ matches a child combinator only when the parent is the immediate parent
              expected true to equal false
            ✗ distinguishes the child combinator from the descendant combinator
              expected true to equal false
fixed     SPEC FILE VERDICT: ...style_block_resolve_selectors_spec.spl declared>=29 executed=29 passed=29 failed=0 dropped=0
```

Same `executed` count on both sides, so the difference is real answers changing,
not examples appearing or being dropped.

## Where to look — SUPERSEDED

This section predicted the fix belonged in argument binding for a declared `T?`
parameter, in `src/compiler_rust/compiler/src/interpreter_call/core/`
("the JIT performs the coercion; the interpreter's equivalent step does not").
**That is wrong and cost a prior attempt its whole session.** The JIT performs
no such coercion, and a local `val v: T? = <bare>` reproduces the fall-through
with no argument binding anywhere in the picture.

The real site is the `Pattern::Enum` arm of
`src/compiler_rust/compiler/src/interpreter_patterns.rs`, at its terminal
`Ok(false)`. Reachability was proven by a POSITIVE PROBE rather than by
grepping a name: the pre-existing `SIMPLE_DIAG_OPTION_PATTERN_SHAPE=1` warning,
emitted from that exact function, fires on the minimal repro under `interpret`
and is silent under the JIT.

The open question this report raised — what a `match` with no matching arm
should do — is untouched and still open. It is a genuine hazard (it is what
turned this type error into a wrong answer), but it is a separate change with
its own blast radius and must not be folded in here.

## Still open elsewhere

`src/app/interpreter/control/control/match.spl:228-229` — a separate,
app-level self-hosted interpreter — carries the **same** defect: after
special-casing nil to `None` at `:223-226` it bails with
`if not value.is_enum(): return Ok(nil)`, so flat `Some(x)` over a raw value
matches nothing there too. It was deliberately NOT changed here: that tree is
recorded as unexercisable by specs, so a change to it could not be verified by
any measurement available in this lane, and an unverifiable edit is not a fix.
Filed here so the family is enumerated rather than left to be rediscovered.

The `to_text` rendering of an untagged raw value held in a `T?` remains wrong on
the JIT/native side (`show(42)` on an `i64?` prints a denormal float;
`<value:0x6>` for i64 6). That is the defect the original "corrupt binding"
reading actually saw. It is untouched here — this change is confined to pattern
matching — and it is why any future measurement of this area must compare
VALUES (`x == 42`), never `to_text` output.
