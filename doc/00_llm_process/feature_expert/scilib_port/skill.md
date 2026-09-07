# SciLib Port Feature Expert

## Scope

Own the current SciLib port surfaces under `src/lib/common/science_math/`,
`src/lib/common/linalg/`, `src/lib/nogc_async_mut/{ndarray,linalg,ml}/`, and
the mirrored SciLib scenarios under `test/03_system/feature/scilib/` and
`test/feature/scilib/`.

## Boundaries

- Layer A native bindings live in `science_math/ffi_blas.spl` and
  `science_math/ffi_lapack.spl`.
- Layer B may use raw buffers; Layer C must expose typed wrappers only.
- `Index` is the public positional wrapper; do not hide public methods with an
  underscore merely to bypass primitive-signature checks.
- `BlasHandle`, `NormOrd`, and shared `LinalgError` live in
  `science_math/types.spl`; provider traits live in `common/linalg/`.

## Evidence

Run each plan acceptance scenario once with the admitted binary and retain its
`SPEC FILE VERDICT`.  The current resolver collision for aliased
`LinalgError` patterns is tracked in
`doc/08_tracking/bug/glob_import_shadows_explicit_alias_in_pattern_position_2026-09-06.md`;
do not weaken the singular-path assertion to evade it.

## References

- [Remaining-area plan](../../../03_plan/lib/scilib/ports/scilib_port_remaining_agents.md)
- [SciLib guide](../../../07_guide/lib/scilib/scilib_ndarray_linalg_guide.md)
- [lib layer expert](../../layer_expert/lib/skill.md)
