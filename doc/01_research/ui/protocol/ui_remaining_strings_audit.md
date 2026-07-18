# UI Remaining Stringly-Typed Surfaces — Audit 2026-04-18

Follow-up to Phases 0–10 of the UI Typed Core migration.
Tracking `text`-typed fields that could become typed enums in Phase 11+.

## Methodology

Grepped all `src/lib/common/ui/*.spl` files for `: text` parameter and field
signatures, then cross-checked each finding against the phase 0–10 exclusion
list (WidgetKind, LayoutKind, ThemeId, Spacing, Radius, Action/CommonAction,
SizeClass, Orientation, IconSet, etc.). CSS-rendering internals, free-form
key→value prop bags, user-supplied labels, and regex patterns were excluded as
genuinely arbitrary strings. Wire-protocol fields (`IPC_MAX_FIELD_LEN`,
`FetchResult.headers`) were excluded as inherently open-ended text.

---

## Findings

### High-value (closed value set, wire-stable, S–M effort)

#### F1: MouseButton
- Field: `UIEvent.MouseEvent(x, y, button: text, kind: text)` — `button` field
- File: `src/lib/common/ui/widget.spl:40`
- Comment in source: `"left" | "right" | "middle" | "" (move events)`
- Proposed: `enum MouseButton { Left, Right, Middle, None }` + `to_wire()/from_wire()`
- Wire impact: serializes-as-text; values are stable (4 values documented)
- Effort: S

#### F2: MouseEventKind
- Field: `UIEvent.MouseEvent(x, y, button: text, kind: text)` — `kind` field
- File: `src/lib/common/ui/widget.spl:38–40`
- Comment in source: `"down" | "up" | "move"`
- Proposed: `enum MouseEventKind { Down, Up, Move }`
- Wire impact: serializes-as-text; 3 stable values
- Effort: S
- Note: F1 and F2 land in the same variant; implement together in one change.

#### F3: FocusKind
- Field: `UIEvent.FocusEvent(target_id: text, kind: text)` — `kind` field
- File: `src/lib/common/ui/widget.spl:42–43`
- Comment in source: `"focus" | "blur"`
- Proposed: `enum FocusKind { Focus, Blur }`
- Wire impact: serializes-as-text; 2 stable values
- Effort: S

#### F4: EffectKind
- Field: `EffectResult.effect_kind: text`
- File: `src/lib/common/ui/effect.spl:22`
- Values in use: `"fetch"` (line 77), `"timer"` (line 81), `"log"` (line 73)
- Proposed: `enum EffectKind { Fetch, Timer, Log }` replacing the `text` field
- Wire impact: none — `EffectResult` is internal only (not serialized over IPC)
- Effort: S — 3 call-sites in effect.spl; no wire contract to preserve

### Medium-value (tractable but requires more design work)

#### F5: LifecycleHandlerId (handler registry)
- Fields: `LifecycleHandler.on_mount_id: text`, `on_unmount_id: text`,
  `on_update_id: text`, `on_action_id: text`, `on_focus_id: text`,
  `on_blur_id: text`
- File: `src/lib/common/ui/lifecycle.spl:29–36`
- Builder surface: `with_on_mount(node, handler_id: text)` etc.
  at `src/lib/common/ui/builder.spl:421–445`
- Proposed: a `HandlerId` newtype wrapping `text`, validated at construction,
  plus a `HandlerRegistry` mapping IDs to closures/fn-pointers. The newtype
  alone costs nothing and eliminates bare-string typos.
- Wire impact: serializes-as-text (prop bag); newtype is transparent on the wire
- Effort: M — newtype wrapper is S; full registry design is separate work
- Blocker: no handler registry exists yet; the newtype can land without it

### Low-value or risky (skip or defer)

#### L1: KeyPress key
- Field: `UIEvent.KeyPress(key: text)` at `widget.spl:24`
- Not enumerable: key names are host-platform strings (`"Enter"`, `"ArrowUp"`,
  `"a"`, `"F5"`, …). An enum `KeyCode` would need a `Custom(text)` escape hatch
  covering the majority of real events. Net gain is low.
- Verdict: defer; log as a future RFC if the event layer is overhauled.

#### L2: UIEvent.Action name
- Field: `UIEvent.Action(name: text)` at `widget.spl:28`
- Already addressed: Phase 5 introduced `Action`/`CommonAction`/`IntoAction`.
  `with_on_typed_action()` exists. The raw `name: text` wire field is the
  intentional escape hatch. No further work needed here.
- Verdict: closed by Phase 5.

#### L3: with_validator pattern
- Function: `with_validator(node, pattern: text)` at `builder.spl:401`
- The value is a free-form regex string. Not enumerable.
- Verdict: skip (genuinely arbitrary per audit scope).

---

## Not present in code (prompt hypotheses that did not match)

The following were hypothesised in the audit brief but are absent from the
current source — future phases should not assume they exist:

| Hypothesis | Actual state |
|---|---|
| `text_input(input_type: text)` | Signature is `text_input(id, placeholder)` — no `input_type` param (builder.spl:75) |
| Tooltip placement string | `tooltip(id, content, target_id)` — no placement arg; `TooltipPosition` only in spec docs |
| Tab orientation string | `tabs(id, tab_labels: [text])` — no orientation arg |
| Toast/notification position | No toast-position prop in builder or widget |
| `DialogResult` confirm/cancel | `dialog(id, title, children)` — no result type |
| Cursor widget prop | Cursor only in generated CSS; not a widget-level prop |
| `text_align` / `flex_direction` props | Not widget props; `h_align`/`v_align` in layout_engine are already `i64` constants |

---

## Recommended Phase 11 priorities

**First: F1+F2+F3 (MouseButton, MouseEventKind, FocusKind)** — all three live
in `widget.spl` event variants, have fully documented closed value sets, touch
no wire protocol, and can ship as a single atomic commit. Combined effort is S.
This cleans the entire event layer in one pass.

**Second: F4 (EffectKind)** — purely internal; zero wire risk; eliminates a
stringly-typed field in `EffectResult` that will become a matching pain point
once the effect system grows (e.g. a future `WebSocket` or `LocalStorage`
effect). Effort S, isolated to `effect.spl`.

**Third: F5 (HandlerId newtype)** — the newtype wrapper alone is a one-liner
that eliminates bare-string IDs passed to `with_on_mount` / `with_on_unmount`
etc. Land the newtype now; defer the full registry design to a later phase when
the lifecycle dispatch model stabilises.
