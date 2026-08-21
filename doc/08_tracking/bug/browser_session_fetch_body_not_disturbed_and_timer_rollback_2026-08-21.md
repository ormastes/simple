# Browser session: fetch body is never "disturbed", and a timer-rollback publication check fails

- Date: 2026-08-21
- Status: RESOLVED 2026-08-21 (see final section; one spec pin WAS wrong — line 340 asserted the WHATWG violation)
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

## 2026-08-21 (later) — RESOLVED: both specs green

`browser_session_async_spec.spl`: **25 total, 25 passed** (24 before + one new
neighbour). `browser_session_dom_generation_runtime_spec.spl`: **1 total, 1
passed**. Verified on `bin/release/x86_64-unknown-linux-gnu/simple`.

### 1b. `Response.bodyUsed` is now read-only — `true:false` -> `true:true`

`src/lib/nogc_sync_mut/js/engine/interpreter_object.spl` `set_object_property`:
a write to key `bodyUsed` on an object carrying `__simple_response_host` is
coerced to the value of `__simple_internal_response_body_consumed`. This is
narrower than a generic "read-only property" mechanism (which would touch every
object write) and keeps one source of truth: `_consume_response_body` still
writes `bodyUsed` through the same setter and gets the same answer. Per WHATWG
Fetch (`bodyUsed` is a `readonly attribute` on the `Body` mixin) a sloppy-mode
assignment is ignored, not an error — which is exactly what the spec's
`r.bodyUsed = false; ... r.bodyUsed` now observes.

Neighbour added (`keeps Response.bodyUsed read-only before and after the body
is consumed`): forcing `true` BEFORE a read must not disturb the body (the
read still succeeds) and forcing `false` AFTER must not un-disturb it
(`false:alpha:true`).

### 1c. Spec line 340 DID contradict WHATWG — expectation corrected

The example `resolves http error responses with ok false and readable
metadata` concatenates `r.text() + ':' + r.text()` and pinned
`...:missing:missing`, i.e. a second `text()` re-yielding the body. WHATWG
Fetch §"Body mixin" (`consume body`): *"If object is unusable, then return a
promise rejected with a TypeError"*, where "unusable" means disturbed or
locked, and `text()` disturbs the body. So the second call returns a
**rejected promise** and cannot yield `missing` again. The pin asserted the
violation and was green only while the rule was unimplemented.

Now that the rule is established, the rendering under this engine is
measured: a fulfilled `Response` promise string-concatenates as its value
(`missing` — this engine's long-standing, non-standard convenience, kept), and
a rejected one as `[object Object]`. The pin is now
`...:missing:[object Object]:...` in both trees. This is explicitly a case
where the spec was wrong and the standard is right.

### 1d. Collateral stale pin in the same file (not a WHATWG matter)

`rejects a late old-page response without consuming the new fetch` pinned the
replacement page's fetch id as `fetch-2`. Request ids are
`"{kind}-{self.next_request_seq}"` on ONE per-session sequence
(`browser_session_runtime.spl:3536`): old page `fetch-1`, replacement document
request `document-2`, new page `fetch-3`. It had been failing silently — see
the runner defect below for why it never showed its real message. Pin
corrected to `fetch-3` with a comment.

### 2b. Timer rollback — real root cause was upstream of `advance_time`

The restore-set fix above was real but not the failing one. Both "Rollback …
when publication fails" steps force failure by setting
`session.dom_identity_index = nil` and expect the next runtime-driven
publication to be rejected as `invalid_document`. It was **accepted**: the
rejected scripts set `document.body.innerHTML`, which makes the candidate
*structural*, and `_sync_from_runtime` then publishes with
`replace_document = true` — a path that **mints a fresh identity index** and so
never consulted the (absent) current one. The nil index was laundered into a
successful commit, and every "leak" (title, body, history, sessionStorage,
cookie, and later the timer's cookie) was committed for real. The second
`advance_time(1)` then returned `0` because the timer had genuinely fired and
published on the first call.

Fix (`browser_session_runtime.spl` `_sync_from_runtime`): a runtime-derived
candidate is only meaningful relative to the document it mutated; with no
current identity index it is rejected as `invalid_document` BEFORE publish,
structural or not, and the existing rollback block restores every mirror.
Loading paths are unaffected: `BrowserSession.new()` and the close-document
path assign the index directly, and every other `publish_dom_snapshot(...,
true, ...)` caller runs on a session that already has one.

### Why the failures were misreported (filed separately)

Both specs reported `expected subject to be truthy, got <falsy>` while the
actual failing matcher was a `to_equal`. `expect(x)` on a falsy subject writes
a *provisional* message into the shared `BDD_FAILURE_MSG` slot unconditionally
(`compiler_rust/compiler/src/interpreter_call/bdd.rs:1103`), overwriting an
earlier genuine matcher failure; a following `.to_equal(0)` clears the
provisional flag but not the clobbered text. Filed as
`doc/08_tracking/bug/spec_runner_provisional_truthy_message_clobbers_real_failure_2026-08-21.md`.
A second engine defect found while writing the neighbour — a nested callback
cannot read its enclosing function's locals/params — is filed as
`doc/08_tracking/bug/js_engine_nested_closure_cannot_read_enclosing_locals_2026-08-21.md`.

### Neighbour sweep

All 39 `test/01_unit/lib/common/web/browser_session*_spec.spl` were run. 26
green. The 13 with failures (`browser_session_spec` 42/89,
`simple_script` 5/5, `wasm_script` 3/3, `form` 2/3, `html_ruby_tags` 2/2,
`http_status` 2/12, `url` 2/5, `loading_history` 1/2,
`script_navigation_scheme_security` 1/1, `wasm_host` 1/107,
`fetch_wasm_chain` no verdict within 900s) were re-run against the pre-change
sources and failed **identically** — pre-existing, not introduced here.

- Status: **RESOLVED**
