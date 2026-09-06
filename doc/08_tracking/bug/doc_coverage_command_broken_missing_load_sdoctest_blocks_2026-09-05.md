# `bin/simple doc-coverage` fails: two exported analysis functions are defined nowhere

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
