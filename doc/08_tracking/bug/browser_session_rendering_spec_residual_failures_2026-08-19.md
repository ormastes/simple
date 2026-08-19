# Residual failures in browser_session dom-input / script-css-animation specs (post interpreter-collision fixes)

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
