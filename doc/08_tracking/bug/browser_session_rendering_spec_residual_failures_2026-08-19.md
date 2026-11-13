# Residual failures in browser_session dom-input / script-css-animation specs (post interpreter-collision fixes)
## OPEN 2026-11-11 — LIVE; not test-runner area; handed back to the JS-engine/browser lane with fresh measured verdicts (P3 runner6 triage)

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Date: 2026-08-19
- Status: OPEN — diagnosed, not yet fixed
- Context: after fixing the CSP `substring` nested-call dispatch
  (`interp_str_substring_nested_call_dispatch_2026-08-19.md`), the local-binding
  shadowing (`local_binding_shadowed_by_cocompiled_global_fn_2026-08-19.md`),
  the CSSValue enum collision
  (`cross_module_cssvalue_enum_collision_2026-08-19.md`), and a spec brace-escaping
  bug, solo verdicts moved:
  - `browser_session_dom_input_spec.spl`: 15/25 -> **19/25**
  - `browser_session_script_css_animation_spec.spl`: 12/25 -> **18/25**

## dom_input — 6 remaining

1. **mixed-case Draw IR text**: layout wraps "Visible İ" mid-word into 5 text
   commands ('Vi','si','bl','e','İ') inside the 24px box
   (`compute_wrap_ranges`/`wrap_line_end` in
   `simple_web_html_layout_renderer_layout.spl` break inside words when no
   space fits — CSS says a single unbreakable word overflows). Spec expects one
   unwrapped `text_value == "Visible İ"` command.
2. **checkbox inline handler `:input:change`**: inline handler `document.title`
   writes lost on the input dispatch composition — already filed:
   `browser_session_input_path_inline_handler_title_writes_lost_2026-08-19.md`.
3/4. **sandbox-blocked form navigation (button + implicit keyboard)**: a
   blocked submit still mutates `current_body_html` — the engine's default
   -action machinery stamps `data-focused`/`data-activated`/`data-submitted`
   attributes into the live DOM (`be_dom_apply_default_action`,
   `dom_accessors.spl:1271`) and the session re-serializes the body
   (double-quoted, attr-sorted), so "document unchanged" assertions fail on
   both content and serialization form.
5. **resets nested controls unless reset canceled**: `expected false to equal
   true` — reset default-action path, same family as 2-4.
6. **blur before focus mutation**: `expected subject to be truthy, got 0` —
   blur/focus composition, same family as the filed input-path bug.

## script_css_animation — 7 remaining

All in the SCRIPTED DOM mutation flush path (`style.cssText` assignment not
reaching the serialized document; scripted body replacement/selector publish;
animation restart from local time zero). The `cssText` ordered-write model
lives in `interpreter_eval_member.spl` (`_host_dom_style_assignment_changes`);
the flush into the session document is where the writes vanish. Overlaps the
open inline-handler-title bug and the in-flight (uncommitted) JS-engine work in
this worktree — coordinate before fixing.


## 2026-11-10 triage (P3 runner lane, work/p3-runner-20261110): LIVE, out of lane scope

Both specs are comprehensively red under the current Rust seed
(bin/simple.exe, this worktree), worse than the 6/7 residuals recorded above:

- browser_session_dom_input_spec.spl: 25 examples, 24 failures
- browser_session_script_css_animation_spec.spl: 25 examples, 25 failures

Every failure carries one common diagnostic:
`semantic: unknown static method new_browser on class JsRuntime` — an
engine API-surface mismatch in the JS-engine/browser-session lane
(spec imports JsRuntime expecting a `new_browser` static the current
src/lib JS engine does not provide). The specific residual mechanisms listed
above are not separately reachable until that import resolves; e.g. the
default-action attribute stamping (dom_accessors.spl:1306-1310) is unchanged.

Not fixed in this lane: the defect lives in sibling-owned engine code
(src/lib JS engine / browser engine), and this doc itself says to coordinate
with the in-flight JS-engine work before fixing. Handed back with measured
verdicts for the engine lane.

## 2026-11-11 triage (P3 runner lane, work/p3-runner6-20261111): LIVE — import blocker resolved since 2026-11-10; residuals match the doc's own diagnosis; engine lane owns the fix

Fresh seed-smoke measurement on this base (fresh Rust seed
bin/simple.exe, build-commit 46fe8f6b6def, SIMPLE_LIB=src,
`bin/simple.exe test <spec> --mode=interpreter --no-cache`, 2026-11-11):

- The 2026-11-10 blocker is GONE: `JsRuntime.new_browser` now exists at
  `src/lib/nogc_sync_mut/js/engine/runtime.spl:278` and is called by
  `src/lib/gc_async_mut/web/browser_session.spl:812`. Both specs now execute
  their examples instead of failing every example at import.
- Specs moved: now at `test/02_integration/rendering/`
  (`browser_session_dom_input_spec.spl`,
  `browser_session_script_css_animation_spec.spl`).
- `browser_session_dom_input_spec.spl`: **19/25, 6 failures** — exactly the
  six residuals enumerated in this doc (mixed-case Draw IR text wrapping;
  inline-handler title writes; sandbox-blocked form navigation x2; reset
  default-action; blur-before-focus). The diagnosed mechanisms are reachable
  and unchanged.
- `browser_session_script_css_animation_spec.spl`: **6/25, 19 failures** —
  comprehensively red in the scripted DOM mutation flush path this doc names
  (worse than the 18/25 recorded at filing; the cssText ordered-write flush
  path still drops writes).

Not fixed in this lane: every remaining mechanism lives in the JS-engine /
browser-session engine code (`src/lib/gc_async_mut/web/`,
`src/lib/nogc_sync_mut/js/`), which is outside this lane's test-runner area,
and this doc itself says to coordinate with the in-flight JS-engine work
before fixing. Handed back with the measured verdicts above. Verdict: LIVE —
OPEN, owner: JS-engine/browser lane.

## 2026-11-13 triage (UI batch B, Linux aarch64, release/1.0.0 @ 35144b7f5e93): LIVE, measured, not fixed here

Fresh run on the Rust seed (`simple-seed-v4`, 16G cgroup cap, one spec at a
time):

- `browser_session_dom_input_spec.spl`: **19/25, 6 failures**.
- `browser_session_script_css_animation_spec.spl`: **16/25, 9 failures**
  (6/25 on 2026-11-11, 18/25 at filing).

The failures fall into three groups, and only the third is the engine work
this record describes.

**1. Seed text-slice units, not engine code (1 failure).** dom_input
"should parse mixed-case document tags..." now fails earlier than the wrap
assertion, at the title: `expected Case İ< to equal Case İ`. One extra
character after a two-byte code point is the signature of a byte end offset
applied by a seed that slices by code point (the #7877 switch; see
`text_len_codepoint_switch_2026-11-03.md`; seed reversal `a3dfd43c52e` is not
on release/1.0.0 yet). Re-measure this example on a byte-slicing seed before
touching `compute_wrap_ranges`.

**2. The spec references symbols that do not exist in the tree (4 failures,
css_animation).** These are compile-time lookups, not behaviour:

- `_duplicate_offset_animation_html` not found;
- `_open_raf_promise_microtask_frame` not found (spec line 395);
- `BrowserRuntimeState` has no field `dom_mutation_generation` (line 294);
- `BrowserRuntimeState` has no field `dom_bridge_generation` (line 363).

The spec was landed ahead of (or without) the helper functions and runtime
state fields it uses. That is the same "caller landed, definition never did"
shape found today in the 8K frame-switch lane
(`web_draw_ir_8k_frame_switch_native_build_timeout_2026-08-11.md`).

**3. Engine behaviour (10 failures).** dom_input: inline click handler
(`expected 0 to be greater than 0`), sandbox-blocked form navigation x2
(`data-submitted="true"` stamped into the live DOM), reset default action,
blur-before-focus paint. css_animation: SimpleScript animation-frame CSS
through Draw IR, copied callbacks after body replacement, body replacement
published to selectors in the same callback, retained DOM bridge aliasing
(`expected aliased to equal distinct`), script-added animation restart from
local time zero. These match the mechanisms diagnosed above.

Not fixed in this lane: group 3 is the scripted-DOM flush and default-action
work in `src/lib/gc_async_mut/web/` and `src/lib/nogc_sync_mut/js/` that this
record assigns to the JS-engine/browser lane, group 2 needs that lane to
supply the missing helpers and state fields, and group 1 waits on the seed.
No assertion was changed and no example was skipped. Row stays open.
