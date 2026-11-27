# Lint Lane C findings — lib warning sweep (lintC-20261113)

Scope: `src/lib/**` (9203 .spl files). Method: serial `bin/simple.exe lint` (seed binary).
Baseline inventory taken from the `src/lib/blink` lint closure (34 files, one dir-lint),
which re-reports warnings for its whole import closure — this gives verified coverage for
all touched files with a single re-lint.

## FIXED (this lane)

### W-STR-BRACE-001 (`{`/`}` in string literals -> `{{`/`}}`, behavior-preserving)
Two linter message variants handled (plus a third found on re-verification):
- "not a valid interpolation expression" (full `{...}` candidate quoted): replaced the exact
  flagged text once per line with `{text}`; idempotency guard `(?<!\{)...(?!\})`.
- "`{` followed by a quote / an escape" (precise line:col): doubled the `{` at the arrow
  column after verifying the char at that index is `{`. NOTE: for the "escape" sub-variant
  the arrow column does NOT point at the brace (points near the string start) — the fix
  was applied by locating the single `{` on the flagged line.
- "empty `{}` in string literal" (third variant): doubled both braces (`"{}"` -> `"{{}}"`).
  Only one src/lib site: src/lib/common/json/value.spl:443.

Files fixed (12):
- src/lib/common/string_core.spl (1)
- src/lib/common/json/tokenizer.spl (2)
- src/lib/common/json/value.spl (4 — incl. hand-fixed `"{}"` -> `"{{}}"` at :443)
- src/lib/common/sdn/parser.spl (16)
- src/lib/nogc_async_mut/env/variables.spl (2)
- src/lib/nogc_sync_mut/env/variables.spl (2)
- src/lib/nogc_sync_mut/io_runtime.spl (1)
- src/lib/nogc_sync_mut/io/process_ops.spl (2, escaped `\"` content — fixed by hand)
- src/lib/nogc_sync_mut/lsp/lsp_code_action.spl (1)
- src/lib/nogc_sync_mut/tooling/easy_fix/accessor_rewrite.spl
- src/lib/nogc_sync_mut/tooling/easy_fix/rules.spl
- src/lib/nogc_sync_mut/tooling/easy_fix/rules_helpers.spl
- src/lib/nogc_sync_mut/ui/theme_package.spl

### Visibility warnings (private fn imported cross-module -> mark owner `pub`)
13 owner files, 28 names, all resolved (0 skipped):
- src/lib/common/config_core/host_config.spl (4)
- src/lib/common/plugin/negotiation.spl (1)
- src/lib/common/sdn/parser.spl (1)
- src/lib/common/ui/native_scalar_text.spl (1)
- src/lib/common/ui/theme_registry.spl (1)
- src/lib/nogc_async_mut/cli/cli_util.spl (1)
- src/lib/nogc_async_mut/env/platform.spl (1)
- src/lib/nogc_sync_mut/host_limits.spl (2)
- src/lib/nogc_sync_mut/io/sffi_common.spl (1)
- src/lib/nogc_sync_mut/tooling/easy_fix/accessor_field_access.spl (1)
- src/lib/nogc_sync_mut/tooling/easy_fix/rules.spl (1)
- src/lib/nogc_sync_mut/tooling/easy_fix/rules_errors.spl (4)
- src/lib/nogc_sync_mut/tooling/easy_fix/rules_helpers.spl (6)

### `export use *` — VERIFIED CLEAN
No live wildcard `export use *` exists in src/lib. All matches are either comments
documenting the repo rule (structural/*/__init__.spl, common/ui/draw_ir.spl:870,
gc_async_mut/gpu/browser_engine/gpu_web/dom/__init__.spl:5) or already-explicit
`export use module.{names}` lists. Nothing to convert.

### REQC004 (wildcard-match-arm rationale)
Established suppression idiom exists and is in use (file-level inner attribute):
`#![allow(REQC004)]` — e.g. src/lib/common/render_scene/matrix4.spl:2,
src/lib/gc_async_mut/gpu/browser_engine/js/*.spl. 0 REQC004 diagnostics in the blink
closure; no new suppressions were required for the files touched.

### Follow-up: private-import baseline prune (NOT done in-lane)
25 fns gained `pub` (visibility fixes). `sh scripts/check/check-private-import-baseline.shs
--prune` exceeded the 10-min lane budget (~10 min running, killed, no file written).
Whoever lands this should re-run the prune at branch head and commit the shrunken
`scripts/check/private_import_baseline.txt` in the PR.

## DEFERRED (out of lane protocol / timebox)

Warning classes observed in the closure but NOT in the lane's fix protocol
(mechanical-only classes were specified; these need per-site judgment):
- `primitive_api` (MC-API-001, 75 in blink) — needs `@allow(primitive_api)` + reason or
  API redesign per site.
- `unnamed_duplicate_typed_args` (23 in blink) — positional duplicate-typed call sites;
  rewrite to named calls per site (pattern exists in git history, e.g. a60d36a4158).
- `non_exhaustive_match` (21 in blink) — needs wildcard arms / exhaustiveness decisions.
- `export_outside_init` (15 in blink) — has a "certain" auto-fix; recommend a dedicated
  `--fix` pass.
- `REQC001` (9), `PTAG001` (3), `bare_bool` (2), `COLL006` (1) in blink.

Subdirs NOT covered (lint is ~15 s/file warm, ~3 min per small dir; whole-subdir linting
of the large trees is infeasible in the timebox): `nogc_sync_mut` (2428 files),
`nogc_async_mut` (1941), `gc_async_mut` (1476), `common` (1417), `gc_sync_mut` (869) beyond
the closure covered here. Remaining smaller subdirs untouched. Visibility owners under
`src/compiler/**` and `src/app/**` belong to sibling lanes.

### gc LAYERING GAPS (record, not re-architected)
Not observed directly in this lane's closure beyond prior-lane deferrals
(external_text_io/system_env_core sync modules with no async equivalent). Recorded as
deferred per lane protocol.

## INFRA / CRASH findings
- None: no lint rc>=128, no 60 s hangs, no ERROR-level diagnostics in scoped runs.
- Lint throughput finding: a single-file lint takes ~15 s warm / ~25 s cold; a 34-file
  directory lint ~2.5-3 min (closure-reported warnings are re-emitted per importer).
  Whole-tree linting of the large lib subdirs is infeasible in a 40-min serial lane —
  this is the dominant constraint on lint-sweep coverage.

## SILENT-GAP candidates
- `lint --json` is not pure JSON: human-readable diagnostics (with ANSI escapes) are mixed
  into stdout before the JSONL records, and each warning is re-reported once per importer
  (e.g. 5005 W-STR-BRACE-001 lines -> 172 unique locations). Tooling must de-duplicate by
  (file, line, code).
- W-STR-BRACE-001 variant-2 messages quote "line L column C" that does not match the arrow
  column (arrow column is the 0-based source index; message column differs by +2).
