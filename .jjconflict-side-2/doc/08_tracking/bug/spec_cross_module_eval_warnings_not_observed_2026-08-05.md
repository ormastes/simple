# A spec that selectively imports interpreter-package pieces does not observe cross-file mutable-global writes

- **ID:** BUG-2026-08-05-spec-cross-module-eval-warnings
- **Date:** 2026-08-05
- **Status:** open, reproduced; workaround applied in the affected spec
- **Severity:** low-medium — affects test observability, not the interpreter's
  own correctness (the real interpreter build loads the whole package
  together, where this was not reproduced)

## Summary

`src/compiler/10.frontend/core/interpreter/eval.spl` declares `var
eval_warnings: [text] = []` and exports it plus `eval_get_warnings()` /
`eval_clear_warnings` (the latter exported at `eval.spl:978` but never
actually defined anywhere in the package — separate, pre-existing, minor
issue noted in passing). Sibling files in the same directory
(`eval_tables.spl`, `eval_stmts.spl`) reference `eval_warnings` directly with
no `use` import, relying on same-directory/package co-compilation to resolve
it — which is how the whole interpreter is normally built.

A THIRD-PARTY `.spl` file (e.g. a spec under `test/01_unit/`) that imports
individual pieces from these files via `use compiler.core.interpreter.eval_tables.{...}`
and `use compiler.core.interpreter.eval.{eval_get_warnings}` (or the
wildcard forms `eval_tables.*` / `eval.*`) does NOT observe writes to
`eval_warnings` made by a function imported from `eval_tables.spl` when read
back through `eval_get_warnings()` imported from `eval.spl`: the count reads
back unchanged (0) after a confirmed push. This reproduces identically for
BOTH the pre-existing, already-shipped `report_match_fallthrough` (landed
2026-08-01) and the new `report_match_wildcard_catch` added alongside this
doc — it is not specific to either diagnostic.

A stricter variant: if the importing file imports ONLY from `eval_tables.spl`
(nothing from `eval.spl`), a call into a function that references
`eval_warnings` fails outright with `semantic: variable 'eval_warnings' not
found` — i.e. the symbol does not resolve at all without also importing
something from the file that declares it, and even then, resolves to what
appears to be a separate, per-compilation-unit instance rather than the
single package-global instance the production interpreter build shares.

## Reproduction

Probes (not checked in, scratchpad-only): a `main()` that calls
`match_wildcard_catch_set_enabled(true)`, confirms
`match_wildcard_catch_get_enabled()` returns `true` (so the SAME-FILE
get/set pair works correctly), then calls `report_match_wildcard_catch(...)`
and reads `eval_get_warnings().len()` before/after — the count does not
change. Confirmed identically substituting the pre-existing
`report_match_fallthrough`.

## Where it was found

While adding sspec coverage for the `SIMPLE_SAFETY_PROFILE`-gated
wildcard-catch diagnostic (see `doc/08_tracking/bug/match_enum_fallthrough_silent_2026-08-01.md`
and `strictness_tiers.md` § "Runtime match-exhaustiveness diagnostics").

## Impact / workaround applied

`test/01_unit/compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl`
does not assert on `eval_warnings` content pushed by `report_match_fallthrough`
or `report_match_wildcard_catch`; those functions' message-building halves
(`match_fallthrough_message`, `match_wildcard_catch_message`, both pure) and
their severity-gating halves (`match_fallthrough_get_abort`/`set_abort`,
`match_wildcard_catch_get_enabled`/`set_enabled`, both same-file state) are
tested directly instead, plus a smoke call confirming
`report_match_wildcard_catch` does not throw in either gate state. Full
end-to-end proof that a real `match` on a real value pushes the right message
into `eval_warnings` and that a Deny-severity abort actually halts execution
requires either (a) running inside the production interpreter build (not
possible from a spec, which cannot re-enter its own running interpreter
session without corrupting it — see the "does not resurrect eval_init()"
note in that spec file) or (b) a genuinely self-hosted `bin/simple` — see
`doc/08_tracking/bug/deployed_bin_simple_still_seed_2026-08-05.md`.

## Not investigated here (out of scope)

Root cause — whether this is module-instantiation-per-import-graph,
selective-import tree-shaking creating a private copy of a package-level
`var`, or something else in the module loader. Fixing it is a separate,
possibly load-bearing change to the module system; this doc only records the
observation and the workaround taken in the one spec it affected.

## Related

- `doc/08_tracking/bug/match_enum_fallthrough_silent_2026-08-01.md`
- `doc/08_tracking/bug/deployed_bin_simple_still_seed_2026-08-05.md`
- Memory class: "shim vacuity — specs test a local copy" (same family of hazard)
