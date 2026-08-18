# runtime_surface_spec: `{{`-escaped to_contain red (pre-existing)

- **Date:** 2026-08-17
- **Status:** FIXED 2026-08-18 (root-caused; seed lexer reverted — see "Root cause & fix" below). Deployed `bin/simple` needs a seed rebuild/redeploy to pick it up.
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

## Root cause & fix (2026-08-18)

- **Root cause:** `d7213eb61742` ("land forward deltas from 20 spend-limit-killed
  sessions", 2026-08-17) added a `current_literal_raw` mirror to
  `src/compiler_rust/parser/src/lexer/strings.rs::scan_fstring_impl` that
  preserved `{{`/`}}` VERBATIM whenever a literal contained no `{expr}`
  interpolation (an attempted resolution of
  `string_literal_double_brace_collapse_2026-06-16` choosing its option 1).
  That contradicted the documented contract AND the seed's own pinned tests
  (`lexer_tests_literals.rs::test_interpolated_strings`,
  `fstring_brace_escape_tests::double_braces_collapse_to_one_literal_brace`),
  and broke every `.contains()` needle built with `{{...}}`.
- **Fix:** both endpoints of `scan_fstring_impl` now always emit the collapsed
  `current_literal`; the raw mirror is kept only for expression-scan
  backtracking. Semantics restored: `{{` -> `{`, `}}` -> `}` in every
  double-quoted text literal, interpolated or not.
- **Verification (cargo-built seed `/mnt/data/tmp/cargo-brace-fix/debug/simple`,
  since deployed `bin/simple` predates the fix):** probe `"a{{b}}c"` prints
  `a{b}c` len=5; `cargo test -p simple-parser --lib` brace/interpolation tests
  green; new regression spec
  `test/01_unit/compiler/lexer_brace_escape_spec.spl` `Results: 4 total, 4
  passed, 0 failed`; `runtime_surface_spec.spl` `Results: 3 total, 3 passed,
  0 failed`. Sabotage probe: reintroducing the raw fallback turns the
  regression spec `Results: 4 total, 1 passed, 3 failed`; restoring returns
  both specs green.
- **Deploy note:** `bin/release/<triple>/simple` (the deployed seed) must be
  rebuilt/redeployed for the fix to reach default tooling.
- **Parity note:** the pure-Simple expander
  (`src/compiler/10.frontend/core/string_interpolation_expand.spl::decode_interpolation_brace_escapes`)
  already collapses unconditionally — no change needed there.
- `string_literal_double_brace_collapse_2026-06-16` remains decided the other
  way: the language contract is Python-fstring-style collapse in ALL
  double-quoted literals; literal `{{`/`}}` must be written doubled (or via
  raw strings/concatenation).
