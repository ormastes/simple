# `LspEmitter` / `LspCodeAction` are imported and called but were never implemented

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Date:** 2026-07-28 · **Status:** FIXED 2026-08-17 · **Class:** NEVER-EXISTED (capability gap)
**Found:** triage of `scripts/check/check-dangling-references.shs` findings scoped
to `src/app/cli/**`.

## Symptom

The checker reports, for three separate CLI query modules:

```
src/app/cli/query_check.spl:16:      SYMBOL: imported name `LspEmitter` is declared in no src file
src/app/cli/query_commands.spl:22:   SYMBOL: imported name `LspEmitter` is declared in no src file
src/app/cli/query_commands.spl:22:   SYMBOL: imported name `LspCodeAction` is declared in no src file
src/app/cli/query_navigation.spl:12: SYMBOL: imported name `LspEmitter` is declared in no src file
```

## Referencing sites

| File | Line | Reference |
|---|---|---|
| `src/app/cli/query_check.spl` | 16 | `use std.report.emitter.lsp.{LspEmitter}` |
| `src/app/cli/query_check.spl` | 113, 539, 645 | `val emitter = LspEmitter.default_emitter()` |
| `src/app/cli/query_commands.spl` | 22 | `use std.report.emitter.lsp.{LspEmitter, LspDiagnostic, LspCodeAction, LspTextEdit}` |
| `src/app/cli/query_commands.spl` | 133 | `val emitter = LspEmitter.default_emitter()` |
| `src/app/cli/query_navigation.spl` | 12 | `use std.report.emitter.lsp.{LspEmitter}` |
| `src/app/cli/query_navigation.spl` | 90 | `val emitter = LspEmitter.default_emitter()` |

## Missing targets

1. The module `std.report.emitter.lsp` — **no `report/emitter` directory exists
   anywhere under `src/`** (`find src -path '*report*' -name '*.spl' | grep -i emit`
   is empty). The dangling-reference checker does not flag the MODULE path only
   because its last-two-segment fallback matches the unrelated key `lsp`
   (`src/compiler_rust/lib/std/src/mcp/lsp/mod.spl`).
2. `LspEmitter` — declared in no file, of any type, anywhere in the repo.
3. `LspEmitter.default_emitter()` — no `default_emitter` exists on any LSP type.
4. `LspCodeAction` — declared nowhere.

`LspDiagnostic` and `LspTextEdit` (the other two names on the same import line in
`query_commands.spl`) *do* exist, but in a different module
(`src/compiler_rust/lib/std/src/mcp/lsp/mod.spl`, which declares `Diagnostic`,
`Position`, `Range`, `Location`, `SymbolInfo`, `HoverInfo`, and five
`Lsp*Handler` classes — but no emitter and no `LspCodeAction`). So the import
line as written cannot be satisfied by any single module.

## Git evidence — NEVER-EXISTED, not a deletion victim

Checked against a healthy pre-incident tree from before the jj-conflict-tree
mass-deletion (`6fd7474260c`, the parent of `115803a7aff`):

```
git grep -l 'LspEmitter' 6fd7474260c -- 'src/*.spl'
  src/app/cli/query_check.spl
  src/app/cli/query_commands.spl
  src/app/cli/query_navigation.spl
```

Three hits, all of them the *consuming* import sites — identical to today. There
has never been a commit in which `LspEmitter` was defined. This is an unfulfilled
promise, **not** collateral damage from the conflict-tree push
(`37cda4befdc` / `3f577c312de`).

## Consequence

`query_check`, `query_commands` and `query_navigation` are live code:
`query_navigation` is imported by `src/app/cli/query_rich.spl`, and
`query_commands` is imported by
`src/compiler_rust/lib/std/src/tooling/__init__.spl`. Every code path that
reaches one of the five `LspEmitter.default_emitter()` call sites is
unresolvable. The LSP-shaped output of `simple query --check` /
`--code-actions` / rename cannot ever have worked.

## Not fixed here

Deliberately not guessing an implementation: an emitter type with a
`default_emitter()` constructor plus whatever the five call sites do with the
result is a real design decision, not a repoint. Needs an owner for
`std.report.emitter.lsp`.

## Secondary finding (separate, not fixed)

`src/app/cli/query_check.spl` defines `fn query_check`, but the *live* wiring
goes through a different definition: `src/app/cli/query_diagnostics.spl:11`
also defines `query_check`, and `src/app/cli/query_rich.spl:23` re-exports it
from `query_diagnostics` — not from `query_check.spl`. Nothing in `src/` or
`test/` imports `app.cli.query_check`. So `query_check.spl` looks like a
shadowed duplicate. Left in place rather than deleted, because removing a
~650-line file needs its own verification pass.


---

## Resolution (2026-08-17)

**Reproduced first**, on a Rust seed built fresh this session
(`/mnt/data/cargo-target-native-p1/release/simple`), by running a program whose
only import is the phantom module. `rc` was read from the line after the
command, never through a pipe:

```
error: semantic: Cannot resolve module: std.report.emitter.lsp
rc=1
```

**Root cause.** `src/lib/common/report/` did not exist — `find src/lib -type d
-name report` returned nothing. All three importers
(`src/app/cli/query_check.spl:16`, `query_navigation.spl:12`,
`query_commands.spl:22`) therefore died at module resolution, so the entire
`--format json` half of each module had never executed.

**Fix.** `src/lib/common/report/emitter/lsp.spl` now implements `LspEmitter`
over the real, shipped `json_escape_string` from `std.common.json`. Only
`default_emitter()` and `encode_string()` exist, because only those are ever
called; `encode_string` returns a COMPLETE JSON string literal (quotes
included), which is what every call site needs — they all use it in value
position, e.g. `,"code":{emitter.encode_string(code)}`.

`LspDiagnostic` / `LspTextEdit` were named in `query_commands.spl`'s import list
and referenced nowhere. They were **removed from the import list rather than
invented** — implementing an unused type to silence an import is how the next
version of this bug gets written.

After:

```
OK "a\"b\nc"
rc=0
```

**Two additional defects found while fixing this, both in `query_check.spl`:**

1. It passed a 4th argument (`emitter`) to `_check_closure_capture_text`,
   `_check_ignored_return_text`, `_check_multiline_bool_text`,
   `_check_safety_text` and `_check_visibility_text`, all of which take three
   (`src/app/cli/query_lint_checks.spl:240`, `:486`). Fixed.
2. **`src/app/cli/query_check.spl` has ZERO importers.** It is an obsolete
   predecessor of `src/app/cli/query_diagnostics.spl`, which is what
   `query_rich.spl:23` actually re-exports; every function unique to
   `query_check.spl` now lives in `query_rich_common.spl` / `query_lint.spl`.
   It was repaired rather than deleted only because
   `scripts/check/ui_backend_isolation_baseline.txt:157` references its path
   and that baseline belongs to another lane. **Recommended follow-up: delete
   `src/app/cli/query_check.spl` and drop that baseline line.**

## Artifacts

- Reproducing spec (subprocess-based, with a proven negative control):
  `test/01_unit/app/cli/query_check_lsp_emitter_import_spec.spl`
  - with the fix: `Results: 2 total, 2 passed, 0 failed`
  - with `src/lib/common/report/emitter/lsp.spl` moved aside:
    `Results: 2 total, 0 passed, 2 failed`
- Similar-problem detection gate:
  `scripts/check/check-no-phantom-deep-stdlib-imports.shs` (+ baseline
  `scripts/check/phantom_deep_stdlib_imports_baseline.txt`).

## Why the existing phantom-import guard could not have caught this

`scripts/check/check-no-phantom-module-imports.shs` reports
`PASS — 9755 import(s) checked, 0 new phantom (baselined: 22)` on the BROKEN
tree, and is right to: its own header (lines 19-24) scopes it deliberately to
BARE single-segment roots (`use foo.`), explicitly excluding `use std.x.y` and
delegating those to "the compiler's own resolver". That delegation is what
failed — the resolver only complains when a module is LOADED, so an unimported
or rarely-exercised module ships broken and looks green.

The new gate closes that half by resolving MULTI-segment `std.` paths
statically on disk (`<base>/A/B/C.spl` or `<base>/A/B/C/__init__.spl`, for base
in `src/lib`, `src/std`, and any immediate family subdirectory of either — the
hop that makes both `std.common.json` and `std.fs` resolve). It reports:

```
PASS — 4004 deep import path(s) checked, 0 new phantom (baselined: 115)
```

**115 baselined offenders is a newly quantified class, not a clean bill of
health.** It is a starting ratchet so no NEW phantom deep import can land; the
115 existing ones (e.g. `text_advanced.escape_json`,
`nogc_async_mut.io.cuda_ffi` — which exists only under `gc_async_mut`/
`gc_sync_mut` — and 22 `nogc_async_mut.io.*_ffi` paths) are unfixed and each
represents a code path that cannot execute. That backlog is NOT triaged here.

## Re-verification 2026-08-17 (lane m5a_app_cli) — ALREADY FIXED by content

The doc header is self-contradictory (`Status: OPEN (P1)` on one line,
`**Status:** FIXED 2026-08-17` on another). Content check settles it:

```
$ find src/lib -path '*report/emitter*'
src/lib/common/report/emitter
src/lib/common/report/emitter/lsp.spl

$ grep -n 'class LspEmitter|default_emitter' src/lib/common/report/emitter/lsp.spl
22:class LspEmitter:
25:    static fn default_emitter() -> LspEmitter:
```

The module `std.report.emitter.lsp`, the class `LspEmitter`, and the static
`default_emitter()` all exist, so the doc's central premise ("no
`report/emitter` directory exists anywhere under `src/`") is stale. The three
importing CLI files (`query_check.spl:16`, `query_commands.spl:22`,
`query_navigation.spl:12`) now resolve.

**Caveat worth recording:** `src/lib/common/report/emitter/` is **untracked**
(`git status --short` reports `?? src/lib/common/report/emitter/`, and
`git log -- src/lib/common/report/emitter/lsp.spl` is empty). The fix exists
in the working tree only. If it is not committed it will be lost, and this bug
returns. Whoever owns that lane must commit it.

Not re-closed here beyond this evidence: only `LspEmitter`/`default_emitter`
were checked. `LspCodeAction` (also cited by this doc, imported by
`query_commands.spl:22`) was **not** verified — treat that half as open.
