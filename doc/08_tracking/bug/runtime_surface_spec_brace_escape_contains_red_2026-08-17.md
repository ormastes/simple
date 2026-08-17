# runtime_surface_spec: `{{`-escaped to_contain red (pre-existing)

- **Date:** 2026-08-17
- **Status:** OPEN (pre-existing; not introduced by the module_loader_compat rename)
- **Spec:** `test/01_unit/compiler/loader/runtime_surface_spec.spl` — example
  "runtime facade keeps the curated export list and avoids duplicate
  jit-context instantiation exports": `Results: 3 total, 2 passed, 1 failed`.
- **Evidence of pre-existence:** restoring the exact `origin/main` content of
  the spec, both loader `__init__.spl` files, and `module_loader.spl`, then
  running `bin/simple test <spec> --no-session-daemon` on the same binary
  (`bin/release/x86_64-unknown-linux-gnu/simple`, seed, 2026-08-17 12:58)
  fails the SAME example. The 2026-08-17 filename-collision rename
  (`module_loader.spl` → `module_loader_compat.spl`) changes nothing here.
- **Suspected cause:** the spec's line-31 needle uses `{{...}}` escaping
  (comment dated 2026-08-10 says `{{` verified to render literal `{`). A
  `bin/simple run` probe measured the needle at len=76 — i.e. NEITHER brace
  collapsed — and `contains=false`, while the target line
  (`export use compiler.loader.module_loader_compat.{moduleloader_execute_smf}`,
  74 chars) is verifiably present. The `{{` → `{` collapse the spec relies on
  no longer happens on this binary (engine or seed regression since the
  2026-08-10 verification).
- **Unblock:** fix `{{`/`}}` literal-brace rendering in text literals (or
  confirm intended semantics and update the spec's needle construction, e.g.
  build the needle by concatenation to avoid brace escaping entirely).
