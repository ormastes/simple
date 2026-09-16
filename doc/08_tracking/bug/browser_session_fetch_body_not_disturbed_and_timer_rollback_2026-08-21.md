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
