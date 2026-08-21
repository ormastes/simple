# Browser session: fetch body is never "disturbed", and a timer-rollback publication check fails

- Date: 2026-08-21
- Status: OPEN (genuine product defects; the specs are correct as written)
- Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (tree-walk interpreter)

## 1. `Response` body can be consumed twice — WHATWG Fetch violation

`test/01_unit/lib/common/web/browser_session_async_spec.spl` -> `24 total, 22
passed, 2 failed`. The failing example "consumes text, JSON, blob, and
array-buffer response bodies once" observes, per body kind:

```
actual   ... |true:false|invalid-json| ... text:first>text:second>json:first>blob:first>buffer:first>bad-json:first>
expected ... |true:true|TypeError: Body is unusable| ... text:first>text:second>json:first>json:second>blob:first>blob:second>buffer:first>buffer:second>bad-json:first>bad-json:second>
```

i.e. the second read of an already-consumed body neither rejects with
`TypeError: Body is unusable` nor leaves `bodyUsed` true.

Root cause is a **four-way duplicated JS engine where only one copy implements
the disturbed-body rule**:

| copy | `_consume_response_body` | `"Body is unusable"` |
|---|---|---|
| `src/lib/gc_async_mut/js/engine/interpreter_native.spl` | 5 refs (defined :1278) | 1 |
| `src/lib/gc_sync_mut/js/engine/interpreter_native.spl` | 0 | 0 |
| `src/lib/nogc_async_mut/js/engine/interpreter_native.spl` | 0 | 0 |
| `src/lib/nogc_sync_mut/js/engine/interpreter_native.spl` | 0 | 0 |

The gc_async_mut copy guards correctly: `_consume_response_body`
(`:1278-1298`) checks `__simple_internal_response_body_consumed`, returns
`Err("TypeError: Body is unusable")` on a repeat, and all four body natives
(`_native_response_text` / `_json` / `_blob` / `_array_buffer`) route through
it. The other three copies (e.g. `nogc_sync_mut/...:8572`,
`nogc_async_mut/...:520`) read `body` directly with no consumed flag, so every
read succeeds.

`src/lib/gc_async_mut/web/browser_session.spl:60` imports
`std.js.engine.runtime`, which does not resolve to the guarded copy on this
lane. Fix: make the disturbed-body rule single-sourced rather than porting the
guard three more times — the duplication is the defect.

## 2. `browser_session_dom_generation_runtime_spec.spl` — timer rollback

Same spec file, `1 total, 0 passed, 1 failed`. Two distinct problems, one now
fixed:

- **Fixed 2026-08-21:** the example died with
  `semantic: method '_snapshot_current_history_for_departure' not found on type
  'BrowserSession'`. `browser_session.spl:2525` calls that method, but its
  `impl BrowserSession:` block lives in `browser_session_loading.spl:1486` and
  `browser_session.spl` never imports that partial (only names it in a comment
  at :23). The spec now pulls the partial into the closure explicitly, the same
  way it already pulls `browser_session_runtime.*`. The underlying wiring gap
  in `browser_session.spl` remains: any *other* caller of that method has the
  same latent failure.
- **Still RED:** with the method reachable, the example now fails an actual
  assertion in the "Rollback a timer runtime when publication fails" step
  (spec lines 125-149) with `expected subject to be truthy, got ` (an empty
  text subject) — the timer's `document.cookie='timer=leak'` /
  `document.body.innerHTML='<p>timer</p>'` effects are not observable after the
  identity index is restored. Not yet root-caused.

## Disposition

Both specs are left RED per `.claude/rules/testing.md`. Neither is a stale
source-text pin: #1 asserts the WHATWG Fetch body-disturbed rule and #2 asserts
transactional rollback the session claims to provide.

## No seed (Rust) change is required.

## 2026-08-21 — partly fixed, both parts narrowed

### 1. Disturbed-body rule — IMPLEMENTED on the live copy (spec still RED on one sub-assertion)

The record's own diagnosis was right: the rule existed only in
`src/lib/gc_async_mut/js/engine/interpreter_native.spl`, which is not the copy
this lane resolves to. `_consume_response_body` is now implemented in
`src/lib/nogc_sync_mut/js/engine/interpreter_native.spl` (the 9,145-line copy
that actually serves `_native_response_text/_json/_blob/_array_buffer`), and
all four natives route through it. It uses `get/set_object_property` for the
consumed flag because that copy has no `_get_internal_object_property`.

Measured effect — the rule now fires everywhere it should:

```
before: ...|true:false|invalid-json|... text:first>text:second>json:first>blob:first>...
after:  ...|true:false|TypeError: Body is unusable|... text:first>text:second>json:first>json:second>blob:first>blob:second>buffer:first>buffer:second>bad-json:first>bad-json:second>
```

Every second read now happens AND rejects with `TypeError: Body is unusable`.
The remaining delta is exactly one thing, and it is a DIFFERENT defect:
`true:false` vs the expected `true:true`. The spec writes
`r.bodyUsed = false;` and then reads it back (spec lines 524-548) — per WHATWG
`bodyUsed` is a read-only accessor, so the assignment must be ignored. This
engine copy lets it through. **Remaining gap: make `bodyUsed` non-writable on
Response objects.** Not attempted here: the write goes through the general
member-assignment path, whose blast radius is every property on every object,
and narrowing that safely is its own change.

### A contradiction inside the spec file, left alone deliberately

`browser_session_async_spec.spl:340` asserts that a second `r.text()`
re-yields the body (`...:missing:missing`) — i.e. it asserts the *violation*
that lines 524-548 assert against. It was green only because the rule was
unimplemented; enforcing the rule turned it RED (24 total: 22 passed before,
21 after). A corrected expectation was drafted and **reverted** when it did not
go green: the exact rendering of a rejected promise under `'' + r.text()` was
not established, and guessing an expectation is worse than an honest RED. The
two examples cannot both be right; line 340 is the one that contradicts WHATWG.

### 2. Timer rollback — the restore set was incomplete; fixed, spec still RED

`browser_session_runtime.spl` `advance_time` restored **only**
`self.runtime_state` when `_flush_runtime_side_effects_and_pump_history()`
rejected the DOM candidate. `eval_script`, 40 lines above, restores eight
fields for the identical transaction. So a rejected timer publication leaked
its cookie writes, request queue, warnings and history delta into the session —
precisely the `document.cookie='timer=leak'` residue the spec's "Rollback a
timer runtime when publication fails" step asserts against. `advance_time` now
restores the same set (plus `current_body_html`), with a comment stating the
two sites must not drift apart.

`browser_session_dom_generation_runtime_spec.spl` is **still RED** with the
same `expected subject to be truthy, got ` and has not moved, so this was a
real gap but not the one that fails the assertion. Narrowing for whoever picks
this up: the failing matcher is one of the two `expect(...is_ok()).to_be(true)`
calls (spec lines 88 and 130) — the subject renders EMPTY, not `false`, which
means `is_ok()` is not returning a boolean rather than returning the wrong one.

### 3. The `browser_session.spl` wiring gap is NOT fixable by an import

The record suggests `browser_session.spl` should import the
`browser_session_loading.spl` partial that defines
`_snapshot_current_history_for_departure`. It cannot:
`browser_session_loading.spl:14` imports `browser_session.{BrowserSession, ...}`,
so the edge would be circular. Assembling the closure at the consumer is
inherent to this partial-`impl` layout, not an oversight — any fix is a
restructuring of the partials, not a missing `use` line.
