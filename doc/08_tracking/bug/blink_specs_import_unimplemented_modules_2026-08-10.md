# Four blink specs RED: they import blink modules that do not exist

Date: 2026-08-10
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
Status: CLOSED 2026-08-17 (all four missing owners implemented and verified)
Lane verified: host x86_64-unknown-linux-gnu, `bin/simple` = Rust bootstrap seed,
interpreter path (JIT fell back: `HIR lowering error: Cannot infer field type:
struct 'CompileOptions' field 'mode' [in src/app/test_runner_new/main.spl]`).

## 2026-08-17 implementation closure

The missing form-state and input owners are implemented rather than stubbed.
Focused evidence passed for input events (8/8), hit testing (7/7), and form
state (4/4), including adjacent deepest-child hit selection and form-field
upsert/placeholder preservation.

The paint-tree owner is now also admitted. It shares one traversal across the
Skia recorder and renderer `DisplayList` sinks, suppresses transparent fills,
emits image/form operations, and varies focused form borders. Current
pure-Simple interpreter evidence passed once per scoped criterion:

- `paint_tree_walker_spec.spl`: 6/6;
- `image_paint_spec.spl`: 3/3;
- `form_paint_spec.spl`: 8/8.

The earlier opaque `value is not callable` result was not reproducible against
the final owner and is superseded by these exact green sinks.

## `STATICS_FAILED_KEY` is a red herring — premise falsified

The reported failure mode "four blink specs RED with `STATICS_FAILED_KEY`,
0/1 each" is a **misreading of unrelated console noise**. `STATICS_FAILED_KEY`
has nothing to do with blink or with spec execution.

- It is a sentinel constant in `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:298`
  (`val STATICS_FAILED_KEY: i64 = -1`), used by `declare_module_statics` to signal
  Cranelift **AOT** static-declaration failure without returning `Option<Dict>`
  (which the seed interpreter erases to nil).
- The lines seen in spec output at 305/315 are **source-listing echoes inside a
  compiler warning**, not failures:

  ```
  warning: Common mistake detected: Use <> instead of [] for generics
    --> src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:305:20
  305 |             handles[STATICS_FAILED_KEY] = 1
  ```

  This warning is itself a **false positive**: `handles[K] = 1` is dict
  bracket-assignment on `Dict<i64,i64>`, not a generic-type instantiation. The
  heuristic fires on any `ident[...]` and is emitted on every parse of the
  compiler tree, so it appears in *every* spec run. Secondary defect worth
  filing separately.

No static initializer fails. No `var x = [T]()` defect is involved.

## The actual four RED specs

`SIMPLE_TIMEOUT_SECONDS=3600 bin/simple test test/01_unit/lib/blink`
(relative path, foreground, exit=1, 24 discovered / 24 executed,
`Results: 89 total, 52 passed, 37 failed`).

The four specs blocking the BoxGeometry/BoxModel nesting are exactly the four
`geo.*`/`BoxModel` users other than `block_flow_spec`:

| spec | result | error |
|---|---|---|
| `test/01_unit/lib/blink/form_paint_spec.spl` | FAIL 0/1 | `semantic: Cannot resolve module: std.blink.dom.form_state` |
| `test/01_unit/lib/blink/hit_test_spec.spl` | FAIL 0/1 | `semantic: Cannot resolve module: std.blink.input.event` |
| `test/01_unit/lib/blink/image_paint_spec.spl` | FAIL 0/1 | `semantic: Cannot resolve module: std.blink.paint.paint_tree_walker` |
| `test/01_unit/lib/blink/paint_tree_walker_spec.spl` | FAIL 0/1 | `semantic: Cannot resolve module: std.blink.paint.paint_tree_walker` |

`block_flow_spec.spl` — the fifth `geo.margin_top` user — **PASSES (7 passed)**.

## Root cause

`src/lib/blink/` contains only:

```
css_parser/  dom/{interaction_state.spl,node.spl}  entity/  layout/{block_flow.spl}  url/
```

The imported modules do not exist anywhere in the repo (verified with
`/usr/bin/find src -type d -name blink` → single hit `src/lib/blink`, and
targeted finds for `paint_tree_walker*`, `form_state*` → no blink hits). Absent:

- `src/lib/blink/paint/paint_tree_walker.spl`
- `src/lib/blink/input/event.spl`, `src/lib/blink/input/hit_test.spl`
- `src/lib/blink/dom/form_state.spl`

This is not a module-resolution bug — it is **specs written ahead of the
implementation**. The same pattern accounts for 12 further RED blink specs
(`document`, `flex`, `html_tokenizer`, `html_tree_builder`, `inline_flow`,
`input_event`, `navigation_controller`, `navigation_fetch`, `paint_controller`,
`scroll_manager`, `style_cascade`), plus two distinct failures:
`css_selector_spec` (0/15, `semantic: value is not callable`) and
`dom_node_spec` (0/7, `function dom_tree_new not found`).

## Fix recipe (not applied — real feature work, do not guess)

To turn the four green, implement, in dependency order:

1. `src/lib/blink/paint/paint_tree_walker.spl` — walker producing a
   `DisplayList` of `PaintOp` from a `block_flow` box tree. Consumed by
   `paint_tree_walker_spec`, `image_paint_spec`, `form_paint_spec`.
2. `src/lib/blink/input/event.spl` + `src/lib/blink/input/hit_test.spl` —
   event types and point-in-box hit testing over `block_flow`. Consumed by
   `hit_test_spec`.
3. `src/lib/blink/dom/form_state.spl` — form control state, pairing with the
   existing `dom/interaction_state.spl`. Consumed by `form_paint_spec`.

Read each spec's `use` list for the exact required symbol set before writing —
the specs are the contract. `src/lib/blink/style/**` is under concurrent work by
another agent and is not on this path.

## BoxGeometry / BoxModel nesting viability

Re `doc/08_tracking/bug/three_layoutbox_variants_2026-08-10.md`: **still
blocked, but for a different and clearer reason than recorded.** The four
specs are not failing on a fixable initializer bug — they cannot compile at all
because a third of the blink engine is unwritten. Renaming
`geo.margin_top` → `geo.spacing.margin_top` in them remains unverifiable churn.

However, the nesting **is partially verifiable today**: the change is
mechanically checkable against `block_flow_spec.spl` (PASS, 7 examples, both
spec trees) and `test/01_unit/lib/common/layout/box_model_spec.spl`. A reviewer
willing to accept those two as the oracle can land the nesting and treat the
four RED specs as text-only edits — they are already RED and will stay RED
either way, so the change cannot regress them. That is a judgement call for the
owner of the box-types bug, not an automatic unblock.

## Gap analysis — why nothing caught this

1. **No `SPEC FILE VERDICT` line is emitted for these files at all.** The run
   produced zero `SPEC FILE VERDICT` matches across 24 files. Sweeps that key on
   that line (the documented protocol for trusting a spec run) see *nothing* for
   the entire blink tree — pass or fail. The `dropped=1` improvement in
   `0ff267a366a` covers "declares examples but can't run"; a module-resolution
   failure takes a different path and still emits no verdict line.
2. **The test database never records it.** Every run ends with
   `Warning: Could not load test database: Failed to load test database` (twice),
   so `doc/08_tracking/test/test_result.md` and `test_db.sdn` are not updated
   from these runs. The failures exist only in transient stdout.
3. **The false-positive `[]`-generics warning trains readers to ignore output.**
   It fires on the compiler's own dict assignments on every run, which is
   precisely how it got mistaken for the failure cause here.

## Duplication finding (rule 2)

`test/01_unit/lib/blink/` and `test/unit/lib/blink/` are near-identical mirrors
(24 files each). Two have drifted, and in both cases **`01_unit` is a strict
superset** — the mirror is the stale copy:

- `block_flow_spec.spl` — `01_unit` adds two assertions on
  `b2.computed_rect.top` / `.bottom`; the mirror would stay GREEN under a
  regression in `computed_rect` vertical placement that `01_unit` catches.
- `paint_artifact_spec.spl` — `01_unit` adds a `_item` helper and two `it`
  blocks covering `item_count()`/`chunk_count()`; the mirror asserts neither.

Recommended merge: delete `test/unit/lib/blink/` in favour of
`test/01_unit/lib/blink/`. Not done here — the mirror tree is repo-wide and
deleting one leaf of it is out of scope for this bug.

## Independent re-verification (2026-08-10, second pass)

Re-checked the core claim from a fresh session before touching anything else:

```
/usr/bin/find src/lib/blink -maxdepth 3 -type f -name '*.spl'
```

confirms `src/lib/blink/` contains only `css_parser/`, `dom/{interaction_state.spl,node.spl}`,
`entity/`, `layout/block_flow.spl`, `style/cascade.spl`, `url/url_parser.spl`. All four
paths this doc names as missing were checked directly and are still absent:
`src/lib/blink/paint/paint_tree_walker.spl`, `src/lib/blink/input/event.spl`,
`src/lib/blink/input/hit_test.spl`, `src/lib/blink/dom/form_state.spl`. `find src -type
d -name blink` still returns the single `src/lib/blink` hit. Confirmed: this is a
genuine, precisely-characterized ARCHITECTURAL/feature-gap end-state, not a
misdiagnosis and not something fixable by a compiler change. No code changes made in
this pass — implementing the three missing modules is real feature work (per the doc's
own "Fix recipe ... do not guess" caveat), not bug-triage scope. Status left OPEN.

## 2026-08-17 — SCOPE for the feature work (no code written; do NOT stub)

Status unchanged (OPEN, feature gap). What follows is the precise scope the
earlier passes deferred: the exact API surface, the behavioural contract the
assertions define, and a size estimate. **Read this before writing a line.**

### Why a stub is worse than the RED spec
Every symbol below is reachable by an assertion that constrains its *behaviour*,
not merely its existence. A module that returns fixed values sized to satisfy
these assertions would go green while painting nothing — converting an honest
"unimplemented" signal into a false "implemented" one, in a subsystem where
nothing else is checking. The four RED specs are currently the only record that
a third of the Blink paint/input path is unwritten. Keep them RED until the
behaviour is real.

### Good news: every dependency already exists
Nothing needs inventing underneath these four modules.

| dependency | status |
|---|---|
| `src/lib/common/render_scene/paint_types.spl` | present, 34L — and already declares **exactly** the 4 variants needed: `FillRect`, `DrawBorder`, `DrawText`, `DrawImage` |
| `src/lib/skia/entity/canvas.spl`, `entity/picture.spl` | present, both carry `op_count` — the recorder sink exists |
| `src/lib/skia/entity/{color,geometry}.spl` | present (`sk_color4f`, `SkRect`) |
| `src/lib/blink/layout/block_flow.spl` | present, 540L — `block_flow_spec` PASSES, so the box tree is a trustworthy input |
| `src/lib/blink/dom/interaction_state.spl` | present, 23L — `form_state.spl` pairs with it |
| `src/lib/blink/entity/computed_style.spl` | present, 235L |

### The 4 modules, in dependency order

**1. `src/lib/blink/input/event.spl`** — pure data, no deps. ~60–80 lines.
Surface: `InputEvent`, `EventType`, `Point`, `mouse_event(type, x, y, _, _)`,
`key_event(...)`. `EventType` needs at least `MouseDown` (used directly).

**2. `src/lib/blink/input/hit_test.spl`** — ~120–160 lines. Surface:
`HitTestResult`, `hit_test_empty`, `point_in_rect`, `hit_test`,
`hit_test_event`, `hit_test_ancestors`.
Contract fixed by assertions:
- `hit_test_empty().hit_box_id == -1` (the miss sentinel);
- `point_in_rect(SkRect(0,0,100,100), 50,50) == true`; `(150,50) == false`;
- `hit_test(ctx, 100,50)` on a single box → that box's id;
- **innermost wins**: nested child at the same point returns the CHILD's id (2),
  not the parent's — this is the one real algorithmic requirement (depth-first,
  deepest match, not first match);
- a point outside everything returns the `-1` sentinel;
- `hit_test_event` maps an `InputEvent` to the same result and populates
  `local_x`/`local_y` (box-relative, asserted `>= 0.0`).

**3. `src/lib/blink/dom/form_state.spl`** — ~100–130 lines. Surface:
`FormState`, `FormFieldEntry`, `form_state_empty`, `form_state_set_value`,
`form_state_get_value`, `form_state_with_field`, `form_state_get_placeholder`.
Contract:
- value round-trips by `node_id`; absent node returns `""` (not nil);
- `with_field` **replaces** an existing entry for the same `node_id` —
  `fields.len() == 1` after two writes to node 5, so it is upsert, not append;
- `set_value` **preserves an existing placeholder** (asserted: placeholder
  `"search…"` survives a later `set_value`).

**4. `src/lib/blink/paint/paint_tree_walker.spl`** — the substantial one,
~350–450 lines. Surface: `StyledBox`, `ImageEntry`, `FormFieldPaintEntry`,
`PaintContext`, `paint_tree_new`, `paint_tree_new_with_images`,
`paint_tree_new_with_forms`, `paint_tree`, `collect_display_list`,
`finalize_paint`.

**Design point the specs force, easy to miss: there are TWO paint sinks.**
- `paint_tree_spec` drives a **skia canvas recorder** — `pc.canvas.width/height`
  mirror the viewport, and `finalize_paint(pc)` yields an `SkPicture` whose
  `op_count` is asserted (0 when nothing drawn, 2 after a parent+child walk).
- `image_paint_spec` / `form_paint_spec` drive a **`DisplayList` of `PaintOp`**
  via `collect_display_list`.
A single implementation must serve both; picking one sink and adapting the other
late is the main rework risk here.

Behavioural contract:
- `find_style` returns an Option — `None` for a missing `layout_id`, `Some` when
  present (both branches asserted);
- background with `a > 0` emits a draw op; **`a == 0` emits none** (transparency
  is a real skip, not a transparent draw);
- a 2-box tree emits exactly 2 ops — one per box, no duplicates;
- images: exactly 1 `DrawImage` per registered `ImageEntry`, carrying the
  correct rect (`x,y,w,h` = 0,0,40,20) and `src_url`; a box with no `ImageEntry`
  emits **zero** `DrawImage` ops;
- form input with a value emits `FillRect` + `DrawBorder` + `DrawText(value)`,
  exactly 1 each, `ops.len() >= 3`;
- empty value draws the **placeholder** text instead;
- **focused vs unfocused borders must differ** in colour or width (the spec
  accepts either axis) — this is where a stub returning a constant border is
  caught;
- a button emits `FillRect` + `DrawText(label)`, `ops.len() >= 2`.

### Size estimate
**~650–820 lines of new pure-Simple across 4 files**, plus export wiring
(`src/lib/blink/{paint,input}/` are new directories). Module 4 is roughly half
the total and carries all the risk; modules 1–3 are mostly data plumbing with
one real algorithm (innermost-wins traversal in module 2).

Realistically a **multi-session feature lane**, not a bug fix — consistent with
this doc's original "real feature work, do not guess" caveat. Suggested landing
order is the dependency order above, each module turning its own spec green:
module 2 greens `hit_test_spec`; module 4 greens `paint_tree_walker_spec` and
`image_paint_spec`; modules 3+4 together green `form_paint_spec`.

No `doc/03_plan/` entry added: the scope fits in this record, and a plan doc for
work nobody has scheduled would be speculative.

## 2026-08-17 third-pass re-verification — still a feature gap, unchanged

All four modules the four RED specs import are still absent (checked by direct
`ls`, each returning `No such file or directory`):
`src/lib/blink/paint/paint_tree_walker.spl`, `src/lib/blink/input/event.spl`,
`src/lib/blink/input/hit_test.spl`, `src/lib/blink/dom/form_state.spl`.

Verdict stands from the second pass and is not re-litigated: this is
implementable feature work (three new Blink modules with real paint/hit-test/
form semantics), not a compiler defect and not bug-triage scope. Per
`.claude/rules/testing.md`, the four specs are correct and stay RED as the
record of the gap; they must not be weakened or marked pending. Status OPEN.

## Re-verification 2026-08-17 (stdlib slice G, content-classified)

**STILL-OPEN, confirmed by CONTENT.** `src/lib/blink/dom/` holds only
`interaction_state.spl` and `node.spl` (no `form_state.spl`), and
`src/lib/blink/input/` does not exist at all. The four specs still import modules
with no implementation. Unchanged from the filed evidence.
