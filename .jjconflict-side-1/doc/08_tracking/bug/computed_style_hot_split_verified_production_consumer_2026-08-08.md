# T2: `ComputedStyleHot` split verified — real production consumer confirmed

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Unit: T2, `doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md`
§3 "T2 — Verify/complete the `ComputedStyleHot` hot/cold split".

## Prior status (plan §1, W1 row)

> **NEEDS-INVESTIGATION** — Spec exists
> (`computed_style_hot_split_spec.spl`); no verified pass/fail, no production
> consumer confirmed → **T2**

## Verdict: DONE — spec passes, real production consumer confirmed, no delete-or-wire decision needed

### Spec pass/fail

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/computed_style_hot_split_spec.spl`
run via `bin/simple run src/app/test_runner_new/test_runner_single.spl
test/01_unit/lib/gc_async_mut/gpu/browser_engine/computed_style_hot_split_spec.spl
--no-session-daemon --sequential` (binary:
`bin/release/x86_64-unknown-linux-gnu/simple`, the Rust seed —
`bin/simple test` on this spec times out under load, per the plan's
established `test_runner_single.spl` fallback):

```
Results: 4 total, 4 passed, 0 failed
```

All 4 cases green: field-count proportionality (15 hot fields vs. a
~150-field `Style` floor), faithful extraction from a real `Style`, the real
layout display-none fast path consulting only hot fields, and the predicate
correctly flagging an actual `display: none`.

### Production consumer

The spec's own docstring claims "the display-none fast path used by the real
layout code (`simple_web_html_layout_renderer_layout.spl`) works off the hot
struct alone." Verified directly against the real layout file (not the
spec's paraphrase of it):

```
$ grep -n "simple_web_style_hot_is_display_none(computed_style_hot_from" \
    src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl
1260:    if simple_web_style_hot_is_display_none(computed_style_hot_from(st)):
2517:        if simple_web_style_hot_is_display_none(computed_style_hot_from(cst)):
```

Two independent call sites in the real layout pass (not a test file, not a
spec) construct `ComputedStyleHot` from a real `Style` and branch on the hot
predicate. This satisfies the plan's acceptance bar directly — a production
consumer exists, so T2's "explicit delete-or-wire decision" branch does not
apply; nothing needed deleting or wiring that wasn't already wired.

### Why W1 read NEEDS-INVESTIGATION before this unit

The prior status table was written before anyone grepped the real layout
file for the call sites named in the spec's own comment — the claim was
plausible but unverified. This unit's only work was that verification: no
production code changed (`src/lib/gc_async_mut/gpu/browser_engine/
computed_style*.spl` and `style_block.spl` are both untouched by T2).

### Collision note (plan's `[E!]` protocol)

T2 lists `style_block.spl` as an `[E!]` collision file "(consumer wiring
only)". No such wiring was needed here — the confirmed consumer lives in
`simple_web_html_layout_renderer_layout.spl`, not `style_block.spl` — so T2
does not touch `style_block.spl` at all, avoiding any T1/T2 file collision
in practice (T1 landed first regardless, per the plan's serialization
requirement).
