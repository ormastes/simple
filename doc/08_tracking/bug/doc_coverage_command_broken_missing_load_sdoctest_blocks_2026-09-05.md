# `bin/simple doc-coverage` fails: two exported analysis functions are defined nowhere
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN
**Filed:** 2026-09-05
**Severity:** MEDIUM — the command is documented in `.claude/rules/commands.md`
and is completely non-functional.

## Reproducer

```
bin/simple doc-coverage
```

exits **1** with:

```
[use-warning] 'load_sdoctest_blocks' is named in
  `use app.doc_coverage.analysis.sdoctest_coverage.{...}` but module
  '<repo>/src/app/doc_coverage/analysis/sdoctest_coverage.spl' does not provide it
  (imported from src/app/cli/doc_coverage_command.spl)
error[E1002]: function `load_sdoctest_blocks` not found
  = help: check the function name or import the module that defines it
```

`bin/simple doc-coverage --missing` is affected identically (same import graph).

## Cause

`src/app/doc_coverage/analysis/mod.spl` re-exports six names under the comment
"Re-export all sdoctest coverage functions". Two of the six have **no definition
anywhere in the tree**:

| export (`analysis/mod.spl`) | `fn <name>(` definitions under `src/app/doc_coverage/` |
|---|---|
| `load_sdoctest_blocks` (:13) | **0** |
| `extract_function_names_from_code` | 1 |
| `match_functions_to_sdoctest` | 1 |
| `compute_sdoctest_coverage` | **0** |
| `suggest_missing_tags` | 1 |
| `validate_tag_format` | 1 |

The four that exist are all in
`src/app/doc_coverage/analysis/sdoctest_coverage.spl`. The nearest thing to the
missing `load_sdoctest_blocks` is
`src/app/doc_coverage/analysis/group_sdoctest.spl:281`
`fn load_sdoctest_blocks_for_module(module_path: text) -> [text]` — a different
name, a different arity, and a different return type.

Live call site, `src/app/doc_coverage/compiler_warnings.spl:218`:

```simple
val sdoctest_data = load_sdoctest_blocks()
val sdoctest_blocks = sdoctest_data.1
```

so the intended signature takes no arguments and returns a tuple whose `.1` is
the block list — i.e. it is NOT a zero-argument wrapper around
`load_sdoctest_blocks_for_module`, and what `.0` should hold is not recoverable
from the call site. `compiler_warnings.spl:10` imports it explicitly:
`use app.doc_coverage.analysis.sdoctest_coverage (load_sdoctest_blocks)`.

## Why this was not fixed in place

Writing the two missing functions requires knowing the intended semantics of the
tuple (what `.0` is) and of `compute_sdoctest_coverage`, neither of which is
determinable from the surviving code. Aliasing to
`load_sdoctest_blocks_for_module` would change the arity AND drop the `.0`
element, producing a silently wrong coverage number — worse than the current
hard failure. Whoever owns doc-coverage should supply the real definitions, or
delete the exports and the call site together.

## Neighbouring facts, so the fix is not over-scoped

Measured the same session on the same binary (the Rust seed at
`bin/release/aarch64-unknown-linux-gnu/simple`): `--version` OK; `lint` on
`src/lib/common/target.spl` OK (6s, `Lint passed: all files clean`, 13
warnings); `run` on small files OK; `todo-scan` OK (rc 0, 71,755 files scanned,
266 TODOs). `doc-coverage` is the only one of the five that fails.

**Side effect worth knowing:** `todo-scan` rewrites the tracked files
`doc/TODO.md` and `doc/08_tracking/todo/todo_db.sdn` on every run, so it dirties
the working tree even when nothing changed. That is by design (both are listed
as auto-generated in `.claude/rules/structure.md`) but is easy to leave behind
by accident.


## 2026-11-10 triage (P3 runner2 lane, work/p3-runner2-20261110): LIVE -> FIXED in lane

The filed defect (missing `load_sdoctest_blocks` / `compute_sdoctest_coverage`)
was already repaired before this base: both functions exist in
`src/app/doc_coverage/analysis/sdoctest_coverage.spl:96,135` (landed with
merge 9e7e7a526edb, PR #7597). What was still LIVE on this base is the
second, same-file defect recorded in the dupe doc
(`doc_coverage_sdoctest_functions_never_implemented_2026-09-02.md`): the
half-finished `DocItem` migration. `bin/simple doc-coverage` scanned 9233
files and then died with
`error: semantic: class `DocItem` has no field named `has_inline_comment``,
exit 1 — the scanner still produced its own simplified `DocItem`
(`src/app/doc_coverage/scanner/mod.spl`) while the command, analysis and
all four reporters were written against `types.doc_item.DocItem`; one
program containing both structs failed semantic analysis.

Fix (completes the migration at the source):
- `scanner/mod.spl` now builds the shared `types.doc_item.DocItem` via a
  `_scanned_doc_item` helper (kind mapped to `DocKind`, `has_comment` ->
  `has_inline_comment`, `file` -> `file_path`); the duplicate local struct
  and its `export` are gone, so only one `DocItem` remains in the program.
- `compiler_warnings.spl` and `cli/doc_coverage_command.spl` updated to the
  shared struct (`kind_str()` / `DocKind.Function`; the command's
  `has_inline_comment` access at old line 334 is now valid).
- Two latent defects reachable only after the collision fix:
  `reporting/terminal_renderer.spl:149` read `file_cov.file_path`
  (FileCoverage has `path`), and `compute_sdoctest_coverage` never set
  per-file `documented_items`/`missing_docs`, so the scope table and the
  markdown "Top 10 Files" table rendered all-zero Documented/Missing
  columns. Both fixed.

Seed-smoke evidence (Rust seed `bin/simple.exe`, this worktree):
- `bin/simple.exe doc-coverage` -> exit 0, real report: Total Items 75323,
  Documented 31635 (41%), SDoctest Coverage 8796 (11%) — the command
  completes a full run (previously exit 1 before any report).
- `bin/simple.exe test test/01_unit/app/doc_coverage/` -> 17/17 files PASS,
  including the new regression spec `doc_item_pipeline_spec.spl` (4/4;
  forces scanner+analysis+all four reporters into one program and asserts
  the cross-module contract end to end) and the updated
  `compiler_integration_spec.spl` (8/8).

Evidence limits: the per-item `has_sdoctest` annotation write inside
`compute_sdoctest_coverage` is invisible under the test runner because
class field writes on loop-bound items are erased there
(`class_field_access_erased_under_test_runner_2026-08-18.md`, interpreter
lane); the regression spec asserts the aggregate counters instead. A
directory-level summary line ("SDoctest Results: 0 total, 1 failed") prints
even when every file verdict is PASS — a runner reporting quirk, observed
but not chased here. The pre-existing `jit-fallback` of
doc_coverage_command.spl (struct 'Nil' field 'items') remains: the module
runs on the interpreter, ~100-1000x slowdown, but the run completes.
