# Bootstrap Stage 3 module-surface placeholder nil trap (2026-08-01)

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

Open. Stage 4 is blocked because a fresh admitted Stage 3 compiler cannot yet
be produced from the main working copy.

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
