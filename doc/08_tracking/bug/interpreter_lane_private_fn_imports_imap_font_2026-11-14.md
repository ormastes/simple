# Interpreter lane rejects private fns reached through imports (imap, font_provider) — 2026-11-14

**Status:** FIXED (branch `work/caret-red-specs-20261114`).

## Symptom
- `test/01_unit/app/llm_caret/infra_mail_starttls_spec.spl` 5/8:
  `semantic: private fn imap_build_capability of module .../imap/build.spl is not visible to .../infra_mail_starttls.spl`.
- `test/03_system/app/llm_caret/feature/llm_caret_gui_backends_spec.spl` 2/3
  (REQ-004): private `browser_font_family_for_style`,
  `browser_font_family_is_monospace`, `browser_host_has_measured_linux_face_set`
  (`text_layout/font_provider.spl`) and `browser_normal_line_height_px`
  (`text_layout/font_renderer.spl`) imported by the browser_engine renderer.

## Root cause
The seed interpreter's module loader (`check_private_use_names`) makes a
private fn imported from another module FATAL. `imap/__init__.spl` re-exports
builder/parse/type fns that were declared without `pub`; the web-render
commits `165fefa4529`/`6e710f65af5` added private font helpers imported across
modules. The JIT lane never checks this, and the spec child was running on the
JIT (see `test_runner_spec_child_loses_mode_pins_2026-11-14.md`), so it surfaced
once the runner pins worked.

## Fix
Mark the re-exported/imported fns `pub`: every `export`ed fn of
`imap/{build,parse,types}.spl` (42) plus the 4 text_layout fns above.

## Specs
- Reproducers: the two specs above (now 8/8 and 3/3).
- Generalization: `test/01_unit/lib/nogc_sync_mut/imap/imap_facade_visibility_spec.spl`
  (exercises the imap facade surface and font_provider helpers on the interpreter lane).

## Open generalization
A dry scan of braced `use std.X.{...}` imports from `gc_async_mut/gpu/browser_engine`
and `app/llm_caret` found ~200 more private-but-imported fns not in
`scripts/check/private_import_baseline.txt`; they are not fixed here (none broke
these specs). A guard for "private fn named in a cross-module `use`" is the follow-up.
