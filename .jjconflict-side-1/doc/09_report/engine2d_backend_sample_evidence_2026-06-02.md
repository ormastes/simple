# Engine2D Backend Sample Evidence - 2026-06-02

## Scope

This report records the current evidence for the backend-selectable 2D
rendering sample requested by the active GUI hardening lane.

Sample:

- `examples/ui/engine2d_backend_test.spl`

Guide:

- `doc/07_guide/rendering/engine2d_backend_sample.md`

## Current Runtime Evidence

Command:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple run \
  examples/ui/engine2d_backend_test.spl --backend=cpu_simd
```

Outcome:

- selected backend: `cpu_simd`
- active backend reported by `Engine2D.backend_name()`: `cpu_simd`
- exact scene checks: `6/6`
- SIMD evidence: `fill_hits=41`
- result: pass

Command:

```bash
SIMPLE_LIB=src SIMPLE_BIN=src/compiler_rust/target/release/simple \
  src/compiler_rust/target/release/simple run \
  examples/ui/engine2d_backend_test.spl --backend=metal
```

Outcome:

- selected backend: `metal`
- active backend reported by `Engine2D.backend_name()`: `metal`
- exact scene checks: `6/6`
- result: pass

## Fixed Perf/Evidence Bug

Before this hardening pass, the explicit `cpu_simd`/`simd_cpu` path rendered
through the SIMD-instrumented CPU backend but reported the active backend as
`cpu`. That made runtime evidence ambiguous and let backend-specific perf
checks lose the selected lane identity.

`Engine2D` now preserves the selected backend name at the facade boundary, so
the sample and tests report `cpu_simd` for the SIMD CPU lane while keeping the
same underlying renderer.

## Verification

- `src/compiler_rust/target/release/simple check` passed for:
  - `src/lib/gc_async_mut/gpu/engine2d/engine.spl`
  - `examples/ui/engine2d_backend_test.spl`
  - `test/02_integration/rendering/engine2d_backend_spec.spl`
  - `test/02_integration/rendering/metal_engine2d_readback_spec.spl`
  - `test/05_perf/graphics_2d/metal_readback_proof_spec.spl`
- `test/02_integration/rendering/engine2d_backend_spec.spl`: `11/11` passed.
- `test/02_integration/rendering/metal_engine2d_readback_spec.spl`: `2/2` passed.
- `test/05_perf/graphics_2d/metal_readback_proof_spec.spl`: `1/1` passed.
- `find doc/06_spec -name '*_spec.spl' | wc -l`: `0`.

## Boundary

Historical generated-kernel reports such as
`doc/09_report/metal_generated_2d_readback_2026-06-01.md` track a separate
portable generated-kernel submit/readback lane. They are not the authoritative
evidence for this backend-selectable Engine2D sample.
