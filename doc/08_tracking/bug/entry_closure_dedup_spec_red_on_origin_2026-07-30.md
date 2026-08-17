# `entry_closure_physical_source_dedup_spec.spl` is red on origin — diagnosis

- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Spec:** `test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl`
- **Repro:** `timeout 900 bin/simple test test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl`
  (plain invocation, no `SIMPLE_TEST_RUNNER_RUST=1`) → `Results: 15 total, 7 passed, 8 failed`.
  Reproduces against origin's own `src/compiler/80.driver/driver_source_loading.spl`; the one
  intentional uncommitted WC line (`_driver_physical_source_key` at line 178) is unrelated and was
  left untouched.

## Root causes found

1. **Real defect (A):** three of the four "must stay byte-identical" copies of the module-name
   sanitizer still call `mod_path.find(...)`, while the driver copy was updated to
   `_driver_text_index_of(mod_path, ...)`. Genuine source drift, same defect class the file's own
   comment warns about (commit `70a29867bc2` broke this once already).
2. **Stale source-grep (B):** `src/compiler/80.driver/driver.spl` was refactored from a large
   monolith down to a 128-line facade; `me compile()`, `load_sources_impl`, `parse_all_impl`,
   `lower_and_check_impl`, the bucket-set decls, and the entry-closure trace strings all moved to
   `driver_source_pipeline_loading.spl`, `driver_source_pipeline_parsing.spl`, and
   `driver_orchestration.spl`. Every assertion still reads `driver.spl` and finds nothing.
3. **Spec bug, not driver bug (C):** four assertions embed literal Simple import-brace syntax
   (e.g. `"...{Thing}"`, `"...{hm_hash_text}"`, `"...{run_test_cli}"`, `"...{source.path}..."`)
   inside a **non-raw** string literal. Simple's `"...{expr}..."` is real interpolation syntax, so
   the literal braces get evaluated against the *spec's own scope* instead of being asserted as
   text. When the name happens to resolve (`hm_hash_text` is imported in the spec) it silently
   swaps in `<fn:hm_hash_text>`; when it doesn't (`Thing`, `run_test_cli`, `source`) the whole `it`
   body fails to compile with `semantic: variable 'X' not found`, pre-empting every other
   assertion in that block. The spec already knows the fix — line 96 correctly uses `r"phase2:...
   {entry_sources.len()}..."` — the four broken ones just omitted the `r` prefix.

## Per-failure table

| # | Example | Class | Evidence |
|---|---|---|---|
| 1 | keeps absolute workspace punctuation out of native module symbols | **A** — real defect | `module_name_normalizer_body()` diff: driver copy uses `_driver_text_index_of(mod_path, "/src/")` / `.../examples/`; `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl:63,67`, `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:159,163`, `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:104,108` still use `mod_path.find(...)`. Fails the "MUST stay byte-identical" contract stated in the driver's own comment. |
| 2 | keeps colliding bucket keys exact and persistent | **C** — spec bug | `expect(loading).to_contain("use compiler.core.interpreter.hashmap.{hm_hash_text}")` (spec line 73) is not raw; `hm_hash_text` is imported at the top of the spec, so the literal `{hm_hash_text}` interpolates to `<fn:hm_hash_text>`. Runner reports: `... to contain use compiler.core.interpreter.hashmap.<fn:hm_hash_text>`. The literal source (`driver_source_loading.spl:13`) does contain the exact text the author intended — verified by grep. Manually re-checked every other assertion in this block (bucket hashing logic, `.starts_with`/`.contains` marker text, `for existing in bucket.split` absence) against current source: all pass. |
| 3 | registers every logical alias from one cached module result | **B** — stale grep | Needle `"phase2:parse:closure:sources collected={entry_sources.len()} unique={unique_entry_sources.len()}"` (correctly `r"..."`-raw) is verbatim in `src/compiler/80.driver/driver_source_pipeline_parsing.spl:148`, not in `driver.spl` (128 lines, no longer contains it). Same for `unique_entry_sources = _driver_unique_physical_sources(...)`, `parsed_entry_paths.push(...)`, `entry_modules.set(source.module_name, ...)` — all present, just relocated to `driver_source_pipeline_parsing.spl`. |
| 4 | uses bucket sets for every phase-one closure membership role | **B** — stale grep | `var seen_sources/closure_loaded_mods/closure_seen_mods/closure_scanned_paths = _driver_text_bucket_set_new(512)` all verified present in `src/compiler/80.driver/driver_source_pipeline_loading.spl`, absent from `driver.spl`. |
| 5 | scans imports through native text operations | **C** — spec bug | Spec line 110 passes `_driver_entry_import_module_paths("...pub use public.owner.{Thing}\n...")` as a non-raw string; `Thing` is not defined anywhere in the spec scope. Runner reports `semantic: variable 'Thing' not found` — the whole `it` body fails to compile, so the actual behavioral checks (import scanning, comment/doc-string skipping) never execute. The literal-text assertions later in the same block (`loading.contains(".find(")).to_equal(false)`, etc.) were not reached. |
| 6 | keeps command-only tools out of the ordinary CLI entry closure | **C** — spec bug | Spec line 145 passes `"use lazy app.test_runner_new.test_runner_main.{run_test_cli}"` as a non-raw string; `run_test_cli` is not in the spec's scope. `semantic: variable 'run_test_cli' not found` aborts the `it` body before any assertion runs. |
| 7 | keeps every explicit entry walk out of whole-workspace loading | **B** — stale grep | Needle `"if has_project_source and self.ctx.options.mode != CompileMode.Check and not nb_entry_closure:"` verified present in `driver_source_pipeline_loading.spl`, absent from `driver.spl`. The two `to_not_contain` checks (`not nb_entry_closure_pre and ... CompileMode.Aot`, `closure_added`) also still correctly absent everywhere — those wouldn't have failed even against the split files. |
| 8 | fails required closure load parse and HIR errors before later phases | **B + C (C masks B)** | Spec line 202 embeds `"...\"parse error in {source.path} (see [parser_error] output above)\"..."` as a non-raw string; `source` is not in scope → `semantic: variable 'source' not found`, aborting the whole `it` body. This masks what would otherwise *also* be a B-class failure: `driver.find("    me compile() -> CompileResult:")`/`load_sources_impl`/`parse_all_impl`/`lower_and_check_impl` all now live in `driver_orchestration.spl` (`compile()`, line 88), `driver_source_pipeline_loading.spl`, `driver_source_pipeline_parsing.spl`, `driver_hir_pipeline_lowering.spl` respectively — none in `driver.spl` anymore, so `compile_start` etc. would resolve to `-1` and fail `to_be_greater_than(-1)` even with the interpolation bug fixed. |

**Totals: 1 A, 3 B, 4 C** (one C entry, #8, also conceals a B).

## Recommendations

- **#1 (A):** fix the 3 drifted copies (`bootstrap_globals.spl`, `module_lowering.spl`,
  `core_codegen.spl`) to call `_driver_text_index_of(...)` instead of `.find(...)`, restoring the
  byte-identical invariant the comment demands. This is the only item with real behavioral risk —
  the file's own history note says this exact drift previously broke `entry_main_symbol` for
  every out-of-tree entry.
- **#2, #5, #6, #8 (C):** prefix the four literal-text string arguments with `r"..."` (same
  pattern already used correctly at spec line 96) so `{Thing}`, `{hm_hash_text}`,
  `{run_test_cli}`, `{source.path}` are treated as literal text, not interpolation targets. This
  is a one-token fix per site, not a driver change.
- **#3, #4, #7 (B):** update the assertions to read the new split files
  (`driver_source_pipeline_parsing.spl`, `driver_source_pipeline_loading.spl`,
  `driver_orchestration.spl`) instead of `driver.spl`. The behavior itself is intact — verified
  every asserted string still exists, just relocated.
- **#8 residual (B, once C is fixed):** re-point `compile_start`/`load_start`/`parse_start`/
  `hir_start`/`hir_end` lookups at `driver_orchestration.spl` (`me compile()`),
  `driver_source_pipeline_loading.spl` (`me load_sources_impl()`),
  `driver_source_pipeline_parsing.spl` (`me parse_all_impl()`), and
  `driver_hir_pipeline_lowering.spl` (`me lower_and_check_impl()` /
  `fn lower_to_hir_impl()`) respectively — the phase-ordering assertions likely need to span
  multiple files now rather than one contiguous `driver.spl` slice.

## Overall verdict

Mixed. This spec is **not** pure source-grep noise — failure #1 is a genuine, currently-shipping
divergence in duplicated logic that the spec exists specifically to catch, and it is real signal
that should not be ignored. But 7 of 8 failures are process noise: 3 are a mechanical fallout of
the `driver.spl` → multi-file split (fix by repointing paths) and 4 are a self-inflicted spec bug
(missing `r"..."` prefix around literal `{...}` text, the same landmine repeated in four spots).
Recommend treating this spec as currently **load-bearing but badly out of sync with the repo it
tests** — worth repairing all 8 sites (cheap, mechanical) rather than deleting the spec, since
failure #1 shows it still catches something real.

## Reconciliation of failure #1 (added 2026-07-30, after a second analysis pass)

Two independent analyses reached opposite-sounding verdicts on #1. Both are
right about different things, and the combination changes the fix:

- **The drift is REAL as drift.** `80.driver` uses `_driver_text_index_of(...)`
  where 20.hir / 50.mir / 70.backend use `.find(...)`, twice per file. The four
  bodies are otherwise line-for-line identical (including the `char_code_at`
  sanitize loop from the `70a29867bc2` outage, which has already converged).
- **The drift is semantically INERT today.** Both compute BYTE offsets:
  `.find()` is `str::find` in the interpreter
  (`interpreter_method/string.rs:44-49`) and `rt_string_find` documents "returns
  the byte index" (`runtime/src/value/collections.rs:2731`); `rt_string_len`
  counts bytes (`collections.rs:1913`). `split(needle)[0]`'s byte length always
  equals `find(needle)`'s byte offset. The needles `"/src/"` and `"/examples/"`
  are pure ASCII and an ASCII pattern cannot straddle a UTF-8 multibyte
  codepoint. This is provable equivalence, not merely untested. **The
  byte-vs-character bug family does NOT apply here** — neither side indexes by
  character.

So assertion #1 is not detecting a behavioural bug. It is a deliberate
**textual tripwire**: it extracts the normalizer body from all four files via
`module_name_normalizer_body` and requires byte-identity, precisely so that any
divergence trips *before* it becomes semantic. It is doing its job. Classify #1
as **real drift, latent impact** — not "spec noise", and not an active defect.

### Why the obvious fix does not work

A proposed fix was to give each lower-layer file its own local helper
(`_hir_text_index_of`, `_llvm_text_index_of`, `_bootstrap_text_index_of`) with
the same body, since the layering rule forbids importing 80.driver downward.
**That would leave #1 red.** `module_name_normalizer_body` extracts the text
from `    var mod_path = path.replace("\\", "/")` through
`    mod_path.replace("/", ".")` — the compared region CONTAINS the helper call,
so differently-named helpers keep the bodies textually different.

### Real options, none free

1. **Identical helper name in all four files.** Converges the text and keeps the
   hardening. Risk: four same-named private functions in different modules —
   check for the known same-name-across-modules global-registry collision
   behaviour before doing this.
2. **Revert 80.driver's two call sites to `.find(...)`.** Smallest diff, no new
   symbols, converges immediately. Risk: `55db1d3d920` ("harden source-matched
   native worker") swapped `.find` → `_driver_text_index_of` across the whole
   file deliberately. If `.find` misbehaves under self-hosted native codegen,
   this reintroduces the bug the hardening was for — and 80.driver runs through
   that same native path.
3. Weaken/normalize the tripwire — **rejected**. Never loosen an invariant to
   get a green; the tripwire's strictness is its value.

**Recommended next step:** establish whether `.find()` is actually reliable
under pure-Simple native codegen (that determines whether option 2 is safe), and
whether identically-named private helpers collide (that determines whether
option 1 is safe). Do NOT apply either blind — this invariant has already caused
one outage when a single copy was changed in isolation.
