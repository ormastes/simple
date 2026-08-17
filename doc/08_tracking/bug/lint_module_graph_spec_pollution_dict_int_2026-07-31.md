# Specs importing compiler.tools.lint.main gain a file-level failure: "cannot convert dict to int"

**Date:** 2026-07-31
**Severity:** spec-verdict pollution — example results stay correct, but every
affected spec FILE reports one extra failure
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
a test-runner defect: a **wildcard-imported top-level symbol named `main`** makes
`bin/simple test`'s outer pass emit a phantom file-level failure. The lint facade
is merely the messenger — `main.spl:11` wildcard-re-exports `entry_and_fixes.*`,
which declares the lint CLI's own `fn main() -> Int` at :231.

Tracking moved to
`doc/08_tracking/bug/test_runner_wildcard_imported_main_phantom_failure_2026-08-01.md`
(minimal repro, control matrix, next step). The bisect notes below are kept
because they record what was ELIMINATED — do not re-run them.

## Symptom

Any spec that imports `compiler.tools.lint.main` (which pulls the whole
compiler module graph) now ends with:

```
error: semantic: type mismatch: cannot convert dict to int
error: test-runner: spec failed
```

after all its examples pass. Both lint specs show it identically:

- `test/01_unit/compiler/lint/collection_easy_fix_spec.spl` — 3/3 examples
  green at push time (`9feda786614a`), now `4 total, 3 passed, 1 failed`.
- `test/01_unit/compiler/lint/collection_index_mutation_spec.spl` — 6/6
  examples green, `7 total, 6 passed, 1 failed`.

The +1 is the file-level entry, not an example. A green-example/red-file
verdict means CI on these files reads as failing while the code under test is
fine.

## Attribution (partial)

The same error string was traced earlier the same day to
`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:305,312` while
that file was another session's uncommitted WIP; it has since landed and the
working copy matches origin. The types at those lines look consistent
(`val STATICS_FAILED_KEY: i64 = -1`, `handles: Dict<i64, i64>`), and the
file's own :262 comment references a known "interpreter bug as
STATICS_FAILED_KEY above" — so this is likely the interpreter mis-typing a
module-level annotated `val` used as a dict key, not a genuine source error.
`bin/simple check` on the adapter exceeds 300 s (whole-graph check), so exact
attribution is unconfirmed.

## Impact

Any spec whose module graph includes the compiler backend cannot produce a
clean file verdict until this is fixed. The examples themselves still execute
and score.

## Probe result (negative)

The minimal shape does NOT reproduce: a spec with module-level
`val K: i64 = -1` and `handles: Dict<i64, i64>; handles[K] = 1` inside a fn
passes 1/1 with no semantic error. So the trigger is not simply an annotated
module-level `val` used as a dict key — it needs more of the adapter's context
(or lives in a different file altogether; the error line names no file).
Attribution remains unconfirmed. Next candidate probe: bisect by importing
successively larger slices of `compiler.tools.lint.main`'s dependency graph
from a one-example spec until the file-level error appears.

## Bisect results (2026-08-01) — narrowed, not isolated

That probe was run. It did not reach a line, but it eliminated two whole
classes of hypothesis and changed the shape of the problem.

**Minimal trigger is smaller than assumed.** A spec whose entire body is
`use compiler.tools.lint.main.{Linter}` plus one `assert_equal(1, 1)` — no lint
function ever called — reproduces `2 total, 1 passed, 1 failed`. Purely
module-load-time; nothing about the lint API or the specs is involved.

**Per-file bisection of `_LintMain` is structurally impossible as written.**
`compiler.tools.lint.main` re-exports six files under `_LintMain/`
(`config_and_model`, `lint_checks`, `traceability_and_assertions`,
`entry_and_fixes`, `name_lints`, `os_freestanding_lints`) and **every one of
those six does `use compiler.tools.lint.main.*` at its own top** — a mutual
cycle. Importing any single submodule drags the whole family back in. All six
"reproduced individually", but that is an artifact of the cycle and is NOT
per-file evidence. Do not read the earlier per-file results as attribution.

**Every external dependency is clean in isolation.** Imported directly, outside
the cycle: `riscv_rtl_debuggability_lint`, `std.tooling.easy_fix.*`,
`file_ops`/`dir_ops`/`cli_ops`/`std.log`, `compiler.core.ast`,
`compiler.core.parser`, `argument_count`, `collection_patterns`, `star_import`,
`stub_impl`, `wide_public`, `common.text.escape_json`, `fix.rules.registry`,
`lint_primitive_api`, `lint_script_language`, `theme_package`, `param_tag`,
`module_init_literal`, `raw_rt_access`, `leading_operator`, `const_ref_default`,
`bare_primitive_internal`. None reproduce alone.

**The only module-level Dict in the family is innocent on inspection:**
`var _DEPRECATED_PROFILE_ALIAS_WARN_COUNTS: Dict<String, i64> = {}`
(`_LintMain/config_and_model.spl:66`), used via `contains_key` + bracket
read/write — the safe pattern per `dict_native_pitfalls.md`. No duplicate
top-level identifiers exist across the six files that a wildcard re-export
could collide on.

**New structural fact — the runner is two-phase, and the error is in phase 2.**
An outer process spawns a child that actually executes the spec; the child
reports `1 example, 0 failures` — genuinely clean — and exits. Only afterwards
does the outer process do a second pass (co-occurring with loading
`std.nogc_sync_mut.spec.env_detect`) and it is there that
`semantic: type mismatch: cannot convert dict to int` originates. A control
spec with no lint import shows the same two-phase structure but stays silent.
So the defect is in what the OUTER pass does when re-processing a file whose
graph includes `compiler.tools.lint.main` — not in the child's execution, and
not in any single declaration.

**Next probe:** break the cycle in a disposable copy — strip the
`use compiler.tools.lint.main.*` self-import from `name_lints.spl` and
`os_freestanding_lints.spl` (each appears to define only self-contained
classes/fns; confirm zero use of `main.*` in their bodies first), then re-run
the same methodology per file to get genuine single-file isolation.

**Note on tooling:** `bin/simple check` is not available as an alternate probe
while the live binary is clobbered — it internally spawns `bin/simple run` and
dies with `unknown command 'run'`. Use `compile <src> -o <tmp>` instead.
