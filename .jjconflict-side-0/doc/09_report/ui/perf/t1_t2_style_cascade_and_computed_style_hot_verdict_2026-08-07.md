# T1/T2 verdicts — W0 cascade wiring investigation + W1 ComputedStyleHot split (2026-08-07)

Executed per `doc/03_plan/ui/perf/render_perf_replan_parallel_teams_2026-08-07.md`
§3 WAVE 1, units T1 and T2. Both measured against on-disk source verified
byte-identical to `origin/main` at measurement time (`git hash-object` ==
`git rev-parse origin/main:<path>` for every file cited below, fetched fresh).
Binary provenance for every spec run: `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`
(the Rust bootstrap seed — no self-hosted-binary claim is made here).
`uptime` at measurement time: `load average: 11.67, 17.97, 20.52` (2 users).

## Pre-existing plan-premise correction (found before any implementation)

The plan's T2 file list says "Files: `computed_style*.spl` [E]". **No such
file exists anywhere under `src/`.** `ComputedStyleHot` actually lives in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl:798-841`.
More importantly, the plan's §1 W1 row status ("NEEDS-INVESTIGATION... no
production consumer confirmed") is **wrong as of this measurement**:
`simple_web_html_layout_renderer_layout.spl:1133` and `:2341` both call
`simple_web_style_hot_is_display_none(computed_style_hot_from(st))` as the
real display-none fast-path skip check inside the production layout walk.
Grepped and enumerated, not assumed (`grep -rn` over `src/`, excluding the
declaring file itself and the spec).

## T2 verdict: DONE (with one documented vacuous case)

Ran `test/01_unit/lib/gc_async_mut/gpu/browser_engine/computed_style_hot_split_spec.spl`:

```
Results: 4 total, 4 passed, 0 failed
```

- Production consumer: confirmed real, two call sites (above), both inside
  the actual layout-walk hot path, not test-only.
- `it` #2 ("extracts... without losing the display value") and #4 ("flags an
  actual display:none style") are genuine behavioral checks, including a
  negative→positive pair — not vacuous.
- `it` #1 ("carries fewer directly-declared fields than the monolithic
  Style") is a **documentation assertion, not a code-derived one**: it
  compares two hand-written literals, `hot_field_count = 15` against
  `style_field_count_floor = 150`, with no reflection over the actual class.
  Verified by hand-count today: `ComputedStyleHot` declares exactly 15 fields
  (`simple_web_html_layout_renderer_style.spl:798-813`, counted directly:
  display, 4×position_*, visibility_hidden, content_visibility_hidden,
  opacity_pct, fg, width_px, height_px, border_box, overflow_hidden, z_index,
  cold); `Style` declares 199 fields (counted by script over
  `simple_web_html_layout_renderer_style.spl:7-...`). Both literals are true
  today but the assertion is fail-open if either class drifts — flagged, not
  silently accepted as strong, and not weakened.
- Per the plan's own rule ("if no production consumer exists after this
  unit, the unit's deliverable is an explicit delete-or-wire decision, not a
  PARTIAL"): a consumer **does** exist, so the unit's deliverable is the
  verdict itself — **DONE**, no delete-or-wire decision needed.

No code changes were required or made for T2; the split, the extraction, and
the production consumer were already landed prior to this session.

## T1 verdict: investigation-only — wiring not achievable at the scoped size

**Baseline measurement (counter-based, not timed) — corrects the plan's own
baseline claim.** §0 of the plan states the cascade "does exactly two string
compares total (:322, :332)" — that number describes candidate *selection*
in `style_block.spl`'s indexed cascade, not property *application*. The
actual per-declaration property dispatch is `BeDomNode.set_style` at
`src/lib/gc_async_mut/gpu/browser_engine/dom.spl:406-427`, called once per
matched declaration from four sites: `style_block.spl:99,110` (the
non-indexed `apply_rules_to_node` path) and `:321,332` (the indexed path).
`set_style` is an **if/elif chain of up to 9 string compares**
(`display, float, clear, overflow, position, color, background-color,
font-weight, text-align`), each preceded by `.trim().lower()` on the
property name.

**Why the literal wiring described by T1 cannot be done as scoped:**

1. `apply_declarations` (`style_property_id.spl:141-191`) writes
   `ComputedStyleHot`/`Style` fields (the `simple_web_html_layout_renderer_*`
   pipeline). `style_block.spl`'s cascade writes `BeDomNode.style: StyleProps`
   (the `browser_engine` DOM pipeline, `dom.spl:1-30` for the `StyleProps`
   struct). These are two independent style representations with **no live
   conversion path between them** — grepped: zero references to `StyleProps`
   in `simple_web_html_layout_renderer_*`, zero references to `ComputedStyleHot`
   in `style_block.spl`/`dom.spl`.
2. The `Style`/`ComputedStyleHot` pipeline already has its own working,
   already-wired declaration-application mechanism —
   `_apply_decls_dispatch`/`_apply_decls_without_grid` in
   `simple_web_html_layout_renderer_decl_apply.spl` (2200 lines), which
   handles the full 199-field `Style`, not just the 11 properties
   `apply_declarations` knows about. `apply_declarations` is a **narrower,
   parallel, currently-unused** mechanism for the same pipeline, not a
   missing link to `style_block.spl`.
3. `style_property_id.spl`'s own header (lines 23-33) states this
   explicitly and pre-dates this investigation: rewiring
   `style_block.spl`'s cascade "is a larger sweep across the whole
   cascade-application call path and is left out of scope per the W0
   landing note."
4. The one pipeline-agnostic W0 export, `property_id_from_name`
   (`style_property_id.spl:55-81`), was considered as a smaller slice
   (dispatch `set_style` on an int id instead of strings) and **rejected as
   a net regression, not a win**: it is itself an 11-branch string-compare
   chain, so calling it from `set_style` adds up to 11 string compares
   *before* the id compare, on top of the 5 elif branches still needed for
   `float`/`clear`/`background-color`/`font-weight`/`text-align` (not in the
   `PropertyId` table at all — `PROPERTY_ID_UNKNOWN` for all five). Net:
   9 string compares today → up to 16 (11 + 5) after. `PropertyId` only pays
   off when the name→id mapping happens once at declaration-*parse* time
   (in `style_block_parse.spl`'s `CssDecl` construction) and the hot path
   sees only integers — that parse-time change is exactly the "larger
   sweep" the header disclaims, and it would also require extending the
   append-only `PropertyId` table with 5 new ids for properties W0 has never
   covered, renumbering `PROPERTY_ID_UNKNOWN`/`PROPERTY_ID_COUNT` in a file
   whose own comment insists on append-only stability.

**No sabotage test was run** — there is no wiring to sabotage; this is
category (b), "blocked on a named, achievable prerequisite," not a landed
mechanism.

**Honest delta:** ~0 today, same as the plan's own prediction, but for a
different and stronger reason than "already banked" — the win is real (up to
9 string compares per declaration application) but is **not reachable** at
the size T1 was scoped for. It requires:
`CssDecl` in `style_block_parse.spl` gaining a `property_id: i64` field
parsed once at construction, `PropertyId`'s table extended (append-only) to
cover `float`/`clear`/`background-color`/`font-weight`/`text-align`, and
`set_style`'s dispatch (or its caller) switched to consume that id. Filed as
the unblock condition below rather than forced.

## Unblock condition (for a future, correctly-scoped unit)

1. Extend `PropertyId` (append-only) in `style_property_id.spl` with ids for
   `float`, `clear`, `background-color`, `font-weight`, `text-align`.
2. Add `property_id: i64` to `CssDecl` (`style_block_parse.spl`), computed
   once via `property_id_from_name` at parse time — never re-parsed per
   apply.
3. Switch `set_style`'s call sites (`style_block.spl:99,110,321,332`) to pass
   the pre-parsed id, and `set_style` (or a new sibling fn) to dispatch on
   the int, not the trimmed/lowered string.
4. Re-measure with a counter (string-compares avoided per declaration
   application), not a timer.

## Files touched this unit

None under `src/` or `test/` — T1 concluded investigation-only per the
plan's own §2(b) category and the degrade-explicitly convention (§4 rule 9);
T2 required no code change, only running the existing spec. This report is
the only new file.
