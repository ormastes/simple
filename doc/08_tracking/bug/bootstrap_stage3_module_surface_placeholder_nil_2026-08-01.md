# Bootstrap Stage 3 module-surface placeholder nil trap (2026-08-01)

Status: RESOLVED (2026-08-17) — retired as already-fixed in current source.

The prior `OPEN (P1)` header contradicted this file's own final section
("Root cause confirmed in the next session"), which already recorded the fix.
The `re-verified by source inspection` stamp was wrong.

Independently corroborated 2026-08-17 (W1), by reading current source rather
than SHA ancestry: `src/compiler/20.hir/hir_lowering/module_surface.spl:1836-1849`
— `module_surfaces_from_modules`, the exact function the GDB session trapped in
at `+582` on source index 6 of 800 — now nil-checks BOTH boundary values before
any field access (`if source == nil: return Err("invalid source entry at index:
...")`, `if module == nil: return Err("invalid parsed module for source: ...")`),
so the `field access on nil receiver` + SIGILL/132 outcome is converted to a
clean, identity-preserving `Err`. Note what is NOT covered by this retirement:
line 1843 still returns `missing parsed module for source: {module_name}` when no
parsed alias exists for a physical source (the cycle-1 failure), and the
placeholder population lives in the driver's `parse_all_impl`
(`src/compiler/80.driver/**`) — a stage-3 run that fails with THAT message is a
different defect, not a regression of this row.

Separate cost finding in the same function (NOT this row's defect, recorded here
so it is not lost): the alias loop at `module_surface.spl:1864-1890` scans every
`builder.surfaces` entry for each alias that misses both `index_by_name` and
`index_by_path`, calling `module_surface_declaration_matches` — a nine-cardinality
comparison that allocates `.keys()` arrays on both sides — and deliberately does
NOT break on first match (it needs the ambiguity check). That is O(N^2) heavy
comparisons at N ~ 800 modules, CPU-bound with near-flat RSS. A provably
behaviour-preserving prefilter exists: `matches()` requires all nine cardinalities
to be equal, so bucketing surfaces by those nine counts cannot change any verdict,
including the `ambiguous parsed module alias` and `parsed module has no source
surface` outcomes. Not applied: it sits on the stage-3 critical path and cannot be
verified without a stage-3 run, and this phase is NOT the phase where the live
stall was measured (`phase=parse`, see
`stage3_parse_stalls_at_tail_43_files_2026-08-17.md`).

## Status

RESOLVED. Verified by CONTENT grep of current source, not SHA ancestry:

- `src/compiler/80.driver/driver_source_pipeline_parsing.spl:228` sizes the
  parsed-module index as `unique_entry_sources.len() * 2 + 1`;
  lines `283-289` insert via linear probing over the parallel
  `parsed_entry_index_keys: [text]` / `parsed_entry_index_values: [i64]`
  arrays, and lines `321-327` look up the same way, returning a fail-closed
  sentinel on miss.
- The selector is `_driver_text_bucket_index`
  (`src/compiler/80.driver/driver_source_loading.spl:99`), FNV-1a via
  `hm_hash_text` with negative-modulo correction.
- **No `Dict<text, i64>` physical-path cache remains** in `parse_all_impl` —
  that Dict, whose staged-native bracket lookup returned an incorrect index,
  was the confirmed root cause and is gone.

Engine cross-check (stale Rust seed `bin/simple`, mtime 2026-08-16 22:59):
an open-addressing round-trip probe reported `mismatches=0` under BOTH
`SIMPLE_EXECUTION_MODE=interpreter` and `=jit`, so the replacement selector
does not diverge by engine.

The residual 135 HIR semantic diagnostics noted at the end of this file are a
DIFFERENT frontier (Stage-3 closure/import surface) and do not reopen this row.
Stage 4 admission remains tracked there, not here.

## Regression specs (added 2026-08-17)

`test/01_unit/bugs/driver_parsed_module_index_selector_spec.spl` — reproducer
(Group 1: the exact Stage 3 source set, `hir_definitions.spl` at index 6, the
`compiler.hir.hir_definitions` alias missing fail-closed with `-1`, and the
`2n+1` capacity rule) plus a similar-problem detection group generalizing to
the defect CLASS "a text-keyed selector returns an index that is not the one
inserted" (Group 2: 40-key collision pressure at minimum capacity, index-range
containment, long shared-prefix paths, in-place re-insert, and a
`Dict<text, i64>`-vs-array-oracle cross-check — the precise comparison the
pre-fix code failed).

- After: `Results: 10 total, 10 passed, 0 failed`
- Ablation (return the neighbour slot's value, i.e. the original
  wrong-index signature): `Results: 10 total, 2 passed, 8 failed` — both
  groups detect it, so the specs are not vacuous.

## Reproduction authority

- Frozen Rust seed/runtime:
  `build/bootstrap/stage4-spdev-current/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority/`
- Fresh Stage 2 candidate SHA-256:
  `2b354ff08f49858ae475808fb93f88fee56a19bfae51d7e8ded587ed7e0f4fbc`
- Stage 2 evidence:
  `build/bootstrap/stage4-spdev-current/manual-stage2/stage2-cycle3.log`
  and `sanity-cycle3.txt`
- Stage 3 evidence:
  `build/bootstrap/stage4-spdev-current/manual-stage3/stage3-cycle3.log`

Stage 2 compiled 728 objects with zero failures and passed the bootstrap
version, unsupported-command, frontend-smoke, and unchanged-hash sanity gates.
Stage 3 then exited 132 (SIGILL) with:

```text
runtime error: field access on nil receiver
```

## Progression across the bounded cycles

1. The fresh Stage 3 first failed with `missing parsed module for source:
   compiler.hir.hir_definitions`.
2. A canonical-path fallback index did not change that result, proving no
   parsed alias for the physical source existed in the module dictionary.
3. An explicit pre-Stage-4 bootstrap placeholder surface cleared that message,
   but the next consumer dereferenced a nil value and trapped with SIGILL.

The third result reached the mandatory verify/fix cap. Do not repeat the same
Stage 2/3 commands unchanged.

## Required next investigation

Instrument the bootstrap-only `parse_all_impl` placeholder population and
`module_surfaces_from_modules` handoff with the source module name, canonical
path, selected parsed-module key, and surface index. Capture the first nil
consumer with a fresh admitted Stage 2 under GDB. Fix the underlying native
dictionary/value transport rather than adding another alias-specific fallback.

After the fix, rebuild Stage 2/3 from one stable source snapshot and run the
canonical Stage 4 CLI build once. Stage 4 evidence remains absent until that
fresh binary passes admission.

## Resumed GDB investigation

The resumed session captured the fresh Stage 2 candidate under GDB. The trap is
inside `module_surfaces_from_modules` at offset `+582` while processing source
index 6 of 800. The generated code calls the runtime index getter, receives a
nil payload, prints `field access on nil receiver`, and executes `ud2` before
`module_surface_canonical_path` is called.

Retained debugger evidence:

- `build/bootstrap/stage4-spdev-current/manual-stage3/stage3-gdb.log`
- `build/bootstrap/stage4-spdev-current/manual-stage3/stage3-resume-gdb.log`

Three resumed candidates were tested:

1. single-pass placeholder surfaces;
2. field-wise reconstruction in `_driver_unique_physical_sources`; and
3. an explicit nil guard after the struct-valued module dictionary read.

All trapped at the same source index before the intended guard. The field-wise
copy and placeholder experiments were rejected and reverted. The tree again
fails closed with `missing parsed module for source` rather than retaining an
unverified crash workaround.

The remaining root investigation belongs upstream of surface extraction:
capture the exact `SourceFile` and `ParserModule` handles at the end of
`parse_all_impl`, before they are stored in `CompileContext`. Avoid reading the
suspect struct-valued dictionary entry in order to diagnose it; record keys and
parallel scalar metadata instead. The same resumed session exhausted its three
fix cycles, so it did not rebuild again after reverting the experiments.

## Root cause confirmed in the next session

The corruption occurred before module-surface extraction. The optimized
physical-path cache in `parse_all_impl` used `Dict<text, i64>`; staged-native
bracket lookup returned an incorrect index. Retaining parsed modules behind
heap boxes changed the source-index-6 SIGILL into a fail-closed missing-box
diagnostic for the same `hir_definitions.spl` source, isolating the scalar Dict
lookup as the selector fault.

The cache now uses open addressing over parallel `[text]` and `[i64]` arrays,
with capacity `2 * unique_sources + 1`. The final fresh Stage 3 run no longer
trapped, accessed a nil parsed-module box, or emitted `missing parsed module`.
This bug is therefore resolved at its original failure boundary.

The build now exits normally with 135 unique HIR semantic diagnostics later in
the pipeline. Those errors are a separate Stage-3 closure/import-surface
frontier and remain recorded in the session handoff. Final evidence is in
`build/bootstrap/stage4-spdev-current/manual-stage3-cycle3/stage3-cycle3.log`.
