# markers.spl `is_nil` → `== nil`

Status: DONE (verified by probe; no spec coverage exists)

## Fix
`src/os/kernel/log/markers.spl:245` — `if spec.is_nil():` → `if spec == nil:`

HEAD (37cda4befdc) still has `spec.is_nil()`. The working copy already carried the
`== nil` form when this lane opened (alongside an unrelated uncommitted
`MarkerSpec.namespace` → `.ns` field rename). Fix confirmed present and correct;
NOT committed (lane is no-commit).

Backups: `/tmp/markers_backup/markers.spl.wc`, `markers.spl.head`

## Verification tier: probe (no spec coverage)
`test/01_unit/os/kernel/logging/marker_wire_format_spec.spl` exists and imports
`validate`, but `bin/simple test` on it exits 0 having run **ZERO examples** —
no "N examples" line, only lint noise. It provides no coverage.

Probe: `build/markers_probe/probe.spl` — 8/8 identical on default engine and
`SIMPLE_EXECUTION_MODE=interpreter`:

- `[BOOT] entry` → Ok
- `[BOOT] entry cpu=0` → Ok
- `[desktop-e2e] spl_start` → Ok
- `[INFO] [BOOT] entry` → Err(unknown marker: ...)   <- the level-prefix invariant
- `[nope] whatever` → Err
- `""` → Err
- `find_spec("[BOOT] entry")` → non-nil
- `find_spec("[nope] whatever")` → nil

## Notes
- `validate()` currently only checks registry membership; `attrs_schema` is
  declared on MarkerSpec but never validated. Not in scope for this lane.
- Probe landmine: `s!.event` on the `MarkerSpec?` from `find_spec` faults with
  "field access on nil receiver" on a NON-nil Option (default engine, seed).
  `== nil` on the same value is correct. Separate Option-unwrap defect.

## Second `is_nil`-on-Option site found (NOT fixed — outside owned paths)
`src/compiler/70.backend/build_native_pipeline.spl:85`
```
val is_native_target = config.target_cpu.is_nil() or config.target_cpu == Some("native")
```
`target_cpu` is an Option (proved by the `== Some("native")` on the same line),
so this is the same never-runnable defect class.

All other `.is_nil()` call sites in owned src are on types that DEFINE a real
`fn is_nil()` method (`backend_types.spl:292`, `lib/*/runtime_value.spl`) and
are legitimate.
