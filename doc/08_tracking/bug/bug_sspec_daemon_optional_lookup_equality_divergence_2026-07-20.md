# Bug: `simple test` daemon evaluator diverges from `simple run` on `text?`-returning lookup + equality pattern

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

**Date:** 2026-07-20
**Reporter:** DRAWIR-PATCH lane (draw_ir_patch.spl / draw_ir_diff.spl id-map slice)
**Severity:** Correctness (silent false result under `simple test`, only at moderate array scale ~20-30 elements; not reproducible under `simple run`)
**Related:** `doc/03_plan/ui/unified_2d_engine/web_wm_gpu_3d_review_2026-07-20.md` item 7 (DrawIR patch)

---

## Summary

A helper function of the shape "loop over a collection, return the first
matching value as a nilable (`T?`), then compare it with `== nil` / `!=` at
the call site" produces a **different result under the `simple test` daemon
evaluator than under `simple run`**, for collections around ~20-30 elements.
Both evaluators agree at small scale (2-5 elements), which is why this went
unnoticed in existing coverage.

## Reproduction (found, then fixed in NEW code)

While building `src/lib/common/ui/draw_ir_patch.spl`, `draw_ir_patch_commands_equal`
(which flattens two `DrawIrComposition`s and compares commands field-by-field)
called a style-change helper of this shape:

```
fn _draw_ir_patch_style_value(command: DrawIrCommand, key: text) -> text?:
    for prop in command.computed_style:
        if prop.key == key:
            return prop.value
    nil

fn _draw_ir_patch_style_changed(a: DrawIrCommand, b: DrawIrCommand) -> bool:
    if a.computed_style.len() != b.computed_style.len():
        return true
    for prop in a.computed_style:
        val other = _draw_ir_patch_style_value(b, prop.key)
        if other == nil:
            return true
        if other != prop.value:
            return true
    false
```

On a 27-command round-trip fixture (`test/01_unit/lib/common/ui/draw_ir_patch_spec.spl`,
"round-trips a mixed ~30-command composition..."), this reported spurious
`style_changed == true` for `computed_style` entries that were byte-identical
("red" == "red") — **but only under `bin/simple test`**. The exact same
composition, walked with `bin/simple run` (a small standalone probe script),
and a manual field-by-field comparison loop printed inline as debug output
*inside the same `simple test` run*, both agreed the values were equal. Only
the path through the `text?`-returning lookup + `== nil` / `!=` comparison
disagreed.

## Fix applied (new code only)

`_draw_ir_patch_style_changed` in `draw_ir_patch.spl` was rewritten to avoid
returning/comparing a nilable value, using a raw double-loop membership
check instead:

```
fn _draw_ir_patch_style_changed(a: DrawIrCommand, b: DrawIrCommand) -> bool:
    if a.computed_style.len() != b.computed_style.len():
        return true
    for prop in a.computed_style:
        var matched = false
        for other in b.computed_style:
            if other.key == prop.key and other.value == prop.value:
                matched = true
        if not matched:
            return true
    false
```

After this change, `test/01_unit/lib/common/ui/draw_ir_patch_spec.spl` went
from 10/11 to 11/11 under `bin/simple test`, with no change under
`bin/simple run` (which was already green both before and after — confirming
the bug is specific to the daemon evaluator, not the algorithm).

## Known-identical latent defect NOT fixed (scope boundary)

`src/lib/common/ui/draw_ir_diff.spl`'s existing `_draw_ir_style_changed` /
`_draw_ir_style_value` pair has the **exact same shape**:

```
fn _draw_ir_style_value(command: DrawIrCommand, key: text) -> text?:
    for prop in command.computed_style:
        if prop.key == key:
            return prop.value
    nil

fn _draw_ir_style_changed(a: DrawIrCommand, b: DrawIrCommand) -> bool:
    if a.computed_style.len() != b.computed_style.len():
        return true
    for prop in a.computed_style:
        val other = _draw_ir_style_value(b, prop.key)
        if other == nil:
            return true
        if other != prop.value:
            return true
    false
```

This is presumed to carry the identical latent defect (unverified at scale —
`draw_ir_diff_spec.spl`'s fixtures are 2 commands, too small to trigger it).
It was **not** changed as part of this lane: the DRAWIR-PATCH task
constraint (Verdict item 4,
`doc/03_plan/ui/unified_2d_engine/web_wm_gpu_3d_review_2026-07-20.md`)
requires `draw_ir_diff.spl`'s report/API to stay unchanged for existing
consumers pending patch-application being proven; touching an internal
helper's algorithm, even for a bugfix, was judged out of scope for that
additive-only slice and is left for a dedicated follow-up.

## Follow-up item 1 applied (2026-08-10)

`_draw_ir_style_changed`/`_draw_ir_style_value` in `draw_ir_diff.spl` rewritten
to use the same raw double-loop membership check already proven safe in
`draw_ir_patch.spl`'s `_draw_ir_patch_style_changed`, eliminating the
`T?`-returning-lookup + `== nil` comparison shape that triggers the daemon
divergence. `_draw_ir_style_value` was removed (no longer called anywhere in
the file or elsewhere — confirmed via grep). Items 2 (general-class
investigation) and 3 (repo-wide grep for the same shape) remain open as
follow-up; they are a broader engine-characterization effort out of scope for
this file-local fix.

## Follow-up items 2 and 3 investigated (2026-08-10)

### Item 2: scale-threshold micro-benchmark — inconclusive, could not reproduce divergence

Built a binary-search-style micro-benchmark harness (`bin/simple test` daemon,
which per `.claude/rules/testing.md` hard-defaults to the tree-walk
interpreter, vs `bin/simple run`, which uses the Cranelift JIT — the same two
engines implicated by the original repro) exercising the identical shape
(`T?`-returning loop lookup, `== nil` / `!=` comparison at the call site) in
three configurations, all against the pure-Simple self-hosted binary
(`bootstrap/stage3/x86_64-unknown-linux-gnu/simple`, per
`.claude/rules/bootstrap.md`):

1. A single call with an N-element `struct Prop{key,value}` list, N swept
   2..100 (`struct` value type). All 19 sampled N passed under the daemon.
2. Same shape with `class Prop`/`class Command` (heap-allocated, closer to
   `DrawIrCommand`'s reference semantics), N swept 2..100. All 14 sampled N
   passed.
3. An outer loop calling the comparison once per "command pair" (C pairs,
   3-prop style list each — matching the original repro's per-command call
   pattern more closely than a single big-N call), C swept 2..500. All 13
   sampled C passed.

None of these reproduced a divergence. To rule out "the synthetic repro just
isn't faithful enough," the **original buggy code was restored verbatim**
(via `git show 364f44f2d45` — the commit that introduced
`_draw_ir_patch_style_value`/`_draw_ir_patch_style_changed` with the
`== nil` shape) into `draw_ir_patch.spl` as a temporary, uncommitted local
edit, and the real production fixture —
`test/01_unit/lib/common/ui/draw_ir_patch_spec.spl`'s ~30-command
round-trip case, the exact test that reportedly went 10/11→11/11 on the
2026-07-20 fix — was run under `bin/simple test`. Result: **13/13 passed**,
including the round-trip case, with the pre-fix buggy code in place. The
edit was reverted immediately after (`git checkout --
src/lib/common/ui/draw_ir_patch.spl`; `git status` confirmed clean before
proceeding).

This means the divergence, as originally observed on 2026-07-20, either:
- requires a precondition not captured by "array/collection size alone"
  (e.g. a specific daemon warm/cold state, a specific sequence of prior
  test-file compilations sharing the daemon process, or a JIT-tiering
  transition that is timing- rather than size-triggered), or
- was masked as a side effect of unrelated interpreter/JIT fixes landed in
  the three weeks since 2026-07-20 (multiple such fixes are on record, e.g.
  `reference_jit_same_class_overload_dispatch_corrupts.md`,
  `run_vs_test_harness_divergence_2026-07-28.md`).

No scale threshold N was identified because no divergence was reproduced at
any tested scale (2 through 500). This is reported as a genuine negative
result, not a fabricated "safe" verdict — the original 2026-07-20 report
remains the only confirmed occurrence, and follow-up item 1's fix
(`draw_ir_diff.spl` rewrite) should stay in place regardless, since it
removes the suspect shape rather than relying on this inconclusive
non-repro. Anyone re-opening this should first try to reproduce with the
*exact* daemon process state from 2026-07-20 (a fresh `simple test`
invocation with no prior compilations in that daemon session) before
concluding the class of bug is gone.

### Item 3: repo-wide grep narrowed to exact shape — one confirmed match, no test coverage

Narrowed the coarse ~80-file "contains both patterns anywhere" grep to the
exact shape (`fn foo(...) -> T?:` whose body is a `for`-loop returning a
value on match and `nil` on fall-through, **and** a call site immediately
doing `val x = foo(...)` followed by `if x == nil` within 1-3 lines) across
`src/lib/**`:

1. Multiline regex (`rg -U --pcre2`) found 97 function definitions across 70
   files matching the `T?`-returning-loop-lookup half of the shape.
2. Cross-referencing each function name against its call sites for the
   `== nil` check pattern (both `val x = f(...)` \n `if x == nil` and the
   inline `if f(...) == nil` forms) found exactly **one** exact-shape match
   in `src/lib/**`:

```
src/lib/nogc_sync_mut/http_server/h2_server.spl:174-178
fn _h2_session_find_stream(session: H2ServerSession, stream_id: i64) -> H2StreamEntry?:
    for entry in session.streams:
        if entry.stream_id == stream_id:
            return Some(entry)
    return nil

src/lib/nogc_sync_mut/http_server/h2_server.spl:582-584 (_h2_dispatch_stream)
    val entry_opt = _h2_session_find_stream(session, stream_id)
    if entry_opt == nil:
        return session
```

`_h2_dispatch_stream` is called from the HTTP/2 server's main per-connection
frame-processing loop (`session.streams` grows by one per concurrently open
stream), so "moderate scale" here means a connection with tens of
concurrent streams — plausible for a real HTTP/2 client. `find test -iname
"*h2_server*spec*"` returned **zero files**: this code path currently has
no spec coverage at all, let alone one at the ~20-30-stream scale needed to
exercise the suspect shape. Three other call sites of the same function
(lines 493, 522, 557) use the safer `entry_opt != nil` / `?? default`
pattern instead and are not at risk.

No other exact-shape matches were found in `src/lib/**`. (The 3 non-h2
near-miss candidates that matched the def-side pattern but not the call-site
pattern — `resolve_target`, `get_handler`, `find_flag_by_long` and similar —
are called with `!= nil` guards, direct `??` defaulting, or aren't compared
against `nil` at all, so they don't carry this specific defect shape even
though they share the nilable-return idiom.)

**Recommended follow-up (not applied — out of scope to modify runtime
networking code speculatively without a regression spec to prove intent):**
add an `h2_server_spec.spl` covering `_h2_dispatch_stream` with 20+
concurrent streams before touching the implementation, then rewrite
`_h2_session_find_stream`'s call site (or the helper itself) using the same
double-loop-membership pattern proven safe in `draw_ir_patch.spl`, mirroring
item 1's fix.

## Suggested follow-up

1. Rewrite `_draw_ir_style_changed`/`_draw_ir_style_value` in
   `draw_ir_diff.spl` using the same raw double-loop pattern, with a
   regression spec using a computed_style-bearing fixture at ~20+ elements
   to actually exercise the daemon-scale path (the current 2-element fixture
   would not catch a regression).
2. Investigate the general class: does `simple test`'s evaluator handle
   `T?`-returning loop-then-compare patterns incorrectly at moderate
   collection scale generally, or is this specific to `text?`? A
   minimal-repro micro-benchmark (grow an array size N, same shape,
   binary-search the N where the two evaluators start disagreeing) would
   turn this from "observed once" into "characterized," matching the
   project's "recurring problem -> team + tests" policy.
3. Grep for the same `for ... return value / nil` + `== nil` comparison shape
   elsewhere in `src/lib/**` — this is a common idiom and other call sites
   may have the same masked defect at scale.

## Re-verification 2026-08-17 (UI slice) — DOC PARTLY STALE; ROOT CAUSE STILL OPEN

Classified by CONTENT.

**Stale half.** This doc states the workaround was applied only to new code and
that `draw_ir_diff.spl`'s `_draw_ir_style_changed` "carries the identical latent
defect ... not touched here". That is no longer true.
`src/lib/common/ui/draw_ir_diff.spl:67-81` now implements
`_draw_ir_style_changed` with an explicit guard comment at line 68:

    # NOTE: deliberately NOT a `T?`-returning-lookup + `== nil` comparison —
    # that shape diverges between `simple test`'s daemon evaluator and
    # `simple run` at moderate array scale (~20-30 elements).

and a nested key/value scan that never returns a nilable from a per-property
lookup. The sibling `draw_ir_patch.spl:142` guard is likewise still in place.
So **both** known UI call sites are now defended; there is no remaining latent
occurrence of the pattern in `src/lib/common/ui/`.

**Live half.** The workarounds are avoidance, not repair. The underlying
defect — `simple test`'s daemon evaluator disagreeing with `simple run` on a
`text?` lookup compared via `== nil` — is a compiler/test-runner divergence and
was NOT fixed. It remains a silent-wrong-result hazard for any code that uses
the optional-lookup shape, and the two NOTE comments are the only thing keeping
the UI layer off it.

Not proven: the divergence itself was not re-reproduced (it needs a
daemon-vs-run differential at ~20-30 element scale; not run under the
bootstrap-priority constraint). The root cause is outside this slice's files.

Status: OPEN for the evaluator divergence; the UI-layer occurrences are closed.
