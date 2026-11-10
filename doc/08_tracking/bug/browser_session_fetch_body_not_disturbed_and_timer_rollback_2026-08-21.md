# Browser session: fetch body is never "disturbed", and a timer-rollback publication check fails
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## Addendum 2026-11-11 — lane ne3: issue #1 FIXED (source-verified); issue #2
## runtime verification BLOCKED by a known, already-routed P1 seed hazard

Traversed on work/p3-ne3-20261111 (origin/release/1.0.0 tip 93490a99c5d8),
refreshed seed bin/simple.exe (2026-11-11, build-commit 0791c2b7f4a7), all runs
seed-smoke (`SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe bin/simple.exe
test <spec> --mode=interpreter --no-cache`).

**Issue #1 (disturbed body) — FIXED in source.** The single-sourcing direction
this bug demanded has landed: `src/lib/gc_async_mut/web/browser_session.spl:61`
now imports `std.nogc_sync_mut.js.engine.runtime` (tier-explicit import fix
`7f923ed08d39` "fix(lib): make 4 gc_async_mut js.engine.runtime imports
tier-explicit", 2026-11-10, ancestor of this tip), and the nogc_sync_mut engine
copy now implements the guard: `_consume_response_body`
(`src/lib/nogc_sync_mut/js/engine/interpreter_native.spl:8779`) is routed by
all four body natives (`_native_response_text/_json/_blob/_array_buffer`,
:8805/:8813/:8825/:8847) and its comment cites this bug doc. The four-way
duplication itself still exists (gc_sync_mut / nogc_async_mut copies still have
no guard), but the copy this lane resolves to is guarded, which is what the
bug's fix directive ("make the disturbed-body rule single-sourced rather than
porting the guard three more times") required for this consumer. Full
single-sourcing remains desirable follow-up.

**Runtime verification of both issues — BLOCKED on this lane.**
`browser_session_async_spec.spl` now compiles and executes all 24 examples but
every one fails at semantic load with `method 'trim' not found on value of type
enum in nested call context` (log:
`build/review/p3fix-ne3-20261111-logs/row2_async_full.log` in this lane's
worktree), preceded by `warning[enum-bare-name-ambiguous]: enum JsValue is
registered again with a different variant set`. This is the known P1 seed
hazard `seed_enum_variant_bare_name_last_registration_wins_2026_10_19`
(status: fix-implemented-verification-pending) surfacing on the refreshed
seed, already routed to the seed lane by the lib3 traverse lane
(`build/review/p3fix-lib3-20261111.sdn`, host-gap note in
`doc/08_tracking/bug/js_timer_queue_4096_entries_hang_2026-09-01.md`). A
minimal enum-in-nested-call-arg probe passes on this seed, confirming the
blocker is the duplicate JsValue registration, not a regression of the
2026-08-17 `instantiate_class` fix. Grant to finish verification: land the
seed-lane fix for `seed_enum_variant_bare_name_last_registration_wins_2026_10_19`,
redeploy the seed, then re-run both specs with the same seed-smoke command.

**Issue #2 (timer rollback)** — no fix commit identified; cannot be confirmed
either way until the hazard above is cleared. Status stays OPEN.

