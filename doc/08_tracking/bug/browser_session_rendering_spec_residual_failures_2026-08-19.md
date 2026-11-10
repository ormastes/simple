# Residual failures in browser_session dom-input / script-css-animation specs (post interpreter-collision fixes)
## Open 2026-09-16 — needs owner triage

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
