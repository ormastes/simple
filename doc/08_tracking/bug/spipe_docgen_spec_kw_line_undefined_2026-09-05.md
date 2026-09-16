# `spipe-docgen` imported two functions that were defined nowhere — every manual generation aborted

(Two symbols, same defect class, found one after the other: `spec_kw_line`
first, then `scenario_at_is_unconditional_pending`. Both are documented below.)


Date: 2026-09-05. Found while closing the E2 checkbox "Regenerate the manual
through pure-Simple `spipe-docgen`" of
`doc/03_plan/agent_tasks/parent_authoritative_actor_process.md`.

## Symptom

Any call into `generate_feature_doc` failed at semantic analysis:

```
semantic: function `spec_kw_line` not found
```

Because `sspec-maintain documentize` composes its mirror around the
`spipe-docgen` manual (`src/app/sspec_maintain/main.spl:488`
`run_spipe_docgen`), the mirror-regeneration path was dead too — which is why
the committed mirror
`doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md`
had gone stale against its source with no way to refresh it.

## Root cause

`src/app/spipe_docgen/spipe_docgen/generator.spl:7` imports `spec_kw_line` from
`app.spipe_docgen.common`, and calls it at `:149` and `:181` to count and list
`pending "..."` scenarios. The symbol existed in **no** module:

```
/usr/bin/grep -rn --include='*.spl' 'spec_kw_line' src
  -> only generator.spl:7, :149, :181 (one import, two call sites, zero definitions)
```

`app.spipe_docgen.common` is a two-line compatibility re-export of
`app.spipe_docgen.spipe_docgen.common`, which defined the other imported
helpers (`spipe_dbg`, `native_fs_*`) but not this one. Nothing failed at import
time, so the gap only surfaced when the two call sites were reached.

## Fix

Defined the helper for real at
`src/app/spipe_docgen/spipe_docgen/common.spl` (after `native_fs_create_dir`):
a whole-leading-token test that requires a quoted title, matching how
`parser.spl:977 is_scenario_line` recognises `pending `. It deliberately
refuses an empty keyword and refuses identifiers that merely begin with the
keyword's letters (`pending_label = 1`), either of which would silently
reclassify unrelated lines as scenarios.

## Second symbol: `scenario_at_is_unconditional_pending`

With `spec_kw_line` defined, `sspec-maintain documentize` got one step further
and then failed the same way:

```
error[E1002]: function `scenario_at_is_unconditional_pending` not found
```

`generator.spl:8-11` imports it from `app.spipe_docgen.parser` and calls it at
`:138`, `:143` and `:174` to split scenarios into pending vs. active. It too was
defined in no module. Implemented at
`src/app/spipe_docgen/spipe_docgen/parser.spl` next to `scenario_title_at`,
deciding "unconditional" by INDENTATION — a placeholder at the scenario body's
own level always executes; one nested deeper sits under an `if`/`match`/loop and
is a conditional gate, i.e. a real oracle. Docstring bodies are skipped, and the
statement-position rule for the placeholder keywords mirrors
`src/app/sspec_maintain/source_facts.spl:148 _is_pending`.

## Third defect: documentize looked for the staged manual at the wrong path

With both symbols defined, `spipe-docgen` generated the manual and
`sspec-maintain documentize` still failed:

```
sspec-maintain: canonical SPipe manual was not produced at
  build/sspec-maintain/documentize/<hash>/03_system/feature/language/parent_commit_piped_result_spec.md
```

Two path derivations had drifted apart:

- `spipe-docgen` writes to `<out>/` + `output_relative_path(doc)`
  (`generator.spl:90`), which RE-ADDS the `test/` prefix
  (`normalize_spec_relative_path`, `:71`) — proven on disk:
  `<out>/test/03_system/feature/language/parent_commit_piped_result_spec.md`.
- `sspec-maintain` looked at `<staging>/` + `_manual_relative_path(path)`
  (`main.spl:474`), which is `derive_manual_path` minus the `doc/06_spec/`
  prefix and therefore has NO `test/` component.

So documentize could never locate the staged manual for any spec under `test/`
— i.e. for every SSpec in the repo. That is why the committed mirror
`doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md`
had drifted stale (recorded source sha `2e156d74…`, actual `c32c322d…`) with
no working way to refresh it.

Fixed by asking docgen for the layout instead of re-deriving it:
`_staged_manual_relative_path` (`src/app/sspec_maintain/main.spl`) calls
`parse_spipe_file` + `output_relative_path`, and a parse failure is a
fail-closed exit 3, not a silent fallback. After the fix,
`sspec-maintain documentize test/03_system/feature/language/parent_commit_piped_result_spec.spl`
reports `wrote doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md`.

## Observed but NOT fixed

A module importing only `{parse_spipe_file, generate_feature_doc}` and binding
the parsed value fails with `semantic: class `DocBlock` not found in this
scope` — the returned `SspecDoc`'s field types are not reachable through the
public import surface, so callers must also import `DocBlock`. Recorded here
rather than changed, because the two acceptance oracles that motivated this
record do not need it.

## Specs

- Reproducing: `test/01_unit/app/spipe_docgen/spec_kw_line_spec.spl`
  `it "reports a quoted pending scenario as a pending keyword line"` — the exact
  line shape `generator.spl:149` classifies.
- Generalization: same file,
  `it "refuses lines that only start with the keyword's letters"`,
  `it "refuses an empty keyword rather than matching every line"`, and
  `it "classifies other spec keywords with the same rule"` — the adjacent
  misclassification risks the whole-token rule exists to prevent.

## Verification lane caveat

Verified with `src/compiler_rust/target/debug/simple` (current-source Rust seed,
built 2026-09-04 18:13). The sanctioned `bin/release/aarch64-apple-darwin/simple_seed`
(2026-07-25) cannot parse current stdlib source — see
`doc/08_tracking/bug/stale_deployed_binaries_reject_current_language_sspec_scorer_unrunnable_2026-09-05.md`.
