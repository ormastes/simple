# DECISION: do NOT retire `core/interpreter/` — the "excluded from every build" premise is FALSE

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
**Filed:** 2026-08-11
**Supersedes the disposal premise in:**
`doc/08_tracking/bug/interpreter_eval_access_calls_drifted_duplicate_definitions_2026-08-11.md`
**Layer:** `80.driver` — source collection

## The question

`_driver_collect_sources` (`src/compiler/80.driver/driver_source_loading.spl:858`
and `:893`) drops every path containing `/core/interpreter/`,
`/10.frontend/parser/`, `/10.frontend/treesitter`, or `/hir_lowering/async`.
Calling that function directly returns **0** files for interpreter paths against
a **2**-file positive control (`core/lexer.spl`). This was read as "~100 KB of
evaluator source is retained in-tree but excluded from every build", and a
retirement was proposed.

**That reading does not survive contact with four independent measurements.**
The exclusion is scoped to ONE loader in ONE lane. It is not the build.

## Evidence that the package is LIVE

### 1. Specs EXECUTE uniquely-defined functions from inside the excluded directory, and pass

Not source greps — real behavioural assertions against real implementations:

| spec | imports from excluded dir | result |
|---|---|---|
| `test/01_unit/compiler/mir/enum_bare_name_collision_dual_key_spec.spl` | `compiler.core.interpreter.eval_tables.{enum_table_register, enum_table_lookup, enum_table_reset}` | 9/9 green, incl. "keeps BOTH sides of a divergent bare-name contest", "raises the ambiguity flag only on DIVERGENCE" |
| `test/01_unit/compiler/interpreter/compiled_module_adapter_spec.spl` | `compiler.frontend.core.interpreter.compiled_module_adapter.{cmr_register, cmr_lookup, ...}` | 9/9 green, incl. registration/lookup/module-export tracking |

**Shadow-definition control (the fail-open this could otherwise be):** each of
these symbols has exactly ONE definition in `src/`, and it is inside the
excluded directory —

    fn enum_table_register  -> 10.frontend/core/interpreter/eval_tables.spl:723   (only)
    fn cmr_register         -> 10.frontend/core/interpreter/compiled_module_adapter.spl:57 (only)
    fn hm_hash_text         -> 10.frontend/core/interpreter/hashmap.spl:24        (only)

There is no other copy these greens could be coming from. Semantics this
specific cannot pass against an absent module.

### 2. Production compiler modules import from inside the excluded directory

- `src/compiler/80.driver/driver_source_loading.spl:15` — `use compiler.core.interpreter.hashmap.{hm_hash_text}`
- `src/compiler/50.mir/_MirLowering/module_lowering.spl:65` — same import

The file that *carries* the exclusion depends on a module the exclusion drops.

### 3. The MDSOC architecture manifest declares the dependency as INTENDED

`src/compiler/85.mdsoc/feature/codegen/backends/interpreter/__init__.spl`
allow-lists `"core/interpreter/**"` for the interpreter backend adapter, which
exists to make the tree-walk interpreter "uniformly selectable via the compiler
driver's backend selection logic". That is forward intent, not residue.

### 4. The measurement itself is unsound: `_driver_collect_sources` is DUPLICATED, and the other copy has NO exclusion

`src/compiler/80.driver/driver_helpers.spl:84` defines a second, co-compiled
`_driver_collect_sources` (plus `_driver_collect_sources_via_find` at `:123`).
Its filter list is `/test/`, `/tests/`, `/doc/`, `/examples/`, `/verification/`
— **it does not mention `/core/interpreter/` at all**, and it walks via
`rt_dir_list` + `_driver_should_skip_dir` rather than `find`.

Two co-compiled definitions of the same public function, winner decided by name
resolution order — the *identical* defect class the interpreter bug documents
for the evaluator pairs. So "0 files collected" proves only which copy answered
that one call. It does not establish that any real build lane applies the
exclusion. **The disposal premise rests on an unresolved duplicate.**

## Decision

**RETIRE: rejected.** Deleting the package would break two production imports,
two green behavioural spec files, and a declared MDSOC adapter dependency. Every
signal pointing at "dead" was fail-open (`use` warns; zero cross-package
importers ignores sibling preloading; the driver probe hit an ambiguous
duplicate).

**RECONNECT: correct in direction, not executable as one step.** Removing the
exclusion is blocked behind two prerequisites, in this order:

1. **Resolve the `_driver_collect_sources` duplicate first.** Until there is one
   definition, no measurement of what the driver collects means anything, and
   removing the exclusion from one copy changes behaviour unpredictably.
2. **Then the 10 drifted evaluator pairs**, which diverge in BOTH directions on
   8 of 10 — no side is a superset, so there is no blind merge.

**The four grep-specs stay.** `evalops_export_and_text_at`,
`dict_literal_dispatch`, `text_byte_at_dispatch`,
`option_result_method_dispatch` are indeed `rt_file_read_text` + `to_contain`
source greps and are fake behavioural coverage — but they are pinned to source
that is NOT being removed, so deleting them now would only shrink coverage
without replacing it, and would churn both mirrored test trees for nothing. They
should be replaced by real executable specs as part of step 2, not deleted ahead
of it.

## The other three excluded paths: SAME situation, all live

| excluded path | files | live importers |
|---|---|---|
| `/10.frontend/parser/` | 6 | `10.frontend/__init__.spl`, `80.driver/driver_types.spl` |
| `/10.frontend/treesitter` | 8 | `35.semantics/symbol_id/stable_id.spl`, `90.tools/query_api.spl`, `query_helpers.spl`, `query_types.spl`, `compiler/treesitter.spl` |
| `/hir_lowering/async` | 2 | `20.hir/__init__.spl`, `hir.spl`, `hir_lowering.spl`; specs `hir_async_spec.spl`, `hir_async_errors_spec.spl` |

None is superseded; none is retirable. All four exclusions are one lane-scoped
filter, not four independent retirements.

## For the next agent

Three lanes burned hours on `eval_access.spl`/`eval_calls.spl` in one night.
**The file pair is not the problem and must not be deleted.** The tractable next
piece of work is the `_driver_collect_sources` duplicate in
`driver_helpers.spl` vs `driver_source_loading.spl` — resolve that before any
further claim about what the driver does or does not compile.

---

## RESOLVED 2026-08-11 — the duplicate is collapsed; `driver_source_loading.spl` wins

Prerequisite 1 above ("resolve the `_driver_collect_sources` duplicate first")
is now done. Determined by **sabotage with an inverse control**, not by
inspection — `pub` vs bare `fn` was only a hypothesis, since resolution in this
repo has been shown to be filename-order sensitive.

Probe: a spec importing `_driver_collect_sources` from
`compiler.driver.driver_source_loading` and calling it on
`src/compiler/10.frontend/core/interpreter/hashmap.spl`, printing the returned
count and the first result's `path`.

| run | edit | result |
|---|---|---|
| baseline | none | `PROBE_RESULT=0 TAG=NONE` |
| sabotage A | `driver_helpers.spl` copy returns a `SABOTAGE_HELPERS` marker for that path | `PROBE_RESULT=0 TAG=NONE` — **no movement** |
| sabotage B (inverse control) | identical marker in the `driver_source_loading.spl` copy | `PROBE_RESULT=1 TAG=SABOTAGE_LOADING` — **moves** |

Sabotage B is the control proving the probe tracks the file rather than a
constant. **The `driver_source_loading.spl` definition wins; the
`driver_helpers.spl` pair was unreachable.**

### Is the exclusion load-bearing?

It is a **bulk-collect lane filter**, not a build-wide retirement, and that is
the whole reason the package is live:

- Both exclusion sites (`driver_source_loading.spl:858` file branch, `:893`
  find branch) are **inside `_driver_collect_sources` only**. A repo-wide
  `/usr/bin/grep -rn "core/interpreter" src/` returns exactly those two lines.
  `_driver_collect_entry_import_source` — the path that resolves `use` targets —
  does not apply them, so imported interpreter modules still load.
- It sits directly beside the `/10.frontend/core/` allow-list
  (`lexer`/`parser`/`ast`/`tokens`/`types`/`backend_types`/`error`/`frontend`/
  `__init__`), which is unambiguously a deliberate lane split, not residue.
- It is not a build-time optimisation of consequence: the four excluded
  fragments cover 45 of 14,485 `.spl` files (0.31%), ~17.8k lines
  (interpreter 27/12,113, parser 6/1,588, treesitter 10/3,443, async 2/711).
- `git log -S` on the exclusion string returns only `chore(sync)`-class commits,
  so history does not name an author intent beyond the code itself.

**The exclusion is therefore KEPT.** Removing it remains blocked behind
prerequisite 2 (the 10 drifted evaluator pairs), exactly as this record said.

### Collapse

`driver_helpers.spl` lost its `_driver_collect_sources`,
`_driver_collect_sources_via_find`, and the now-dead `_skip_dirs`,
`_driver_should_skip_dir`, `_default_read_source`, `_active_read_source` that
only that copy consumed. No rename was needed: the two behaviours are not both
required, because only one was ever reachable. A pointer comment replaces them.

### Regression pin

`test/01_unit/compiler/driver/driver_collect_sources_single_definition_spec.spl`
(mirrored byte-identically to `test/unit/...`), 4/4 green. **Oracle proven
non-tautological:** restoring the deleted duplicate into `driver_helpers.spl`
turns it **3/4 RED**; with the collapse in place it is 4/4 GREEN.

Pre-existing reds, unchanged by this work and verified at HEAD with the change
reverted: `entry_closure_physical_source_dedup_spec.spl` (daemon-worker-timeout
at HEAD too) and `processing_cuda_backend_spec.spl` (1/4; it reads only
`driver_source_loading.spl`, which this change leaves byte-identical).

**Any claim about what the driver compiles is now meaningful.**
