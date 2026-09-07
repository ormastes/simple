# The RT/HAL general exit-capture surface asserted by its spec exists nowhere in `src/`

**Date:** 2026-09-06
**Found by:** sspec score-80 wave 16C (modernizing
`test/01_unit/compiler/mir/rt_hal_general_exit_capture_source_spec.spl`)

## Symptom

All 3 scenarios in
`test/01_unit/compiler/mir/rt_hal_general_exit_capture_source_spec.spl` are
RED. The spec asserts a provenance / exit-arena / schema-bind / controller-seal
/ V2-exit-codec surface on `src/compiler/50.mir/mir_rt_hal_boundary.spl`.

That file is **115 lines** and defines only:

- `rt_hal_boundary_receipt`
- `rt_hal_boundary_call`
- `inject_rt_hal_boundary`
- `inject_rt_hal_controller_finalize`
- `inject_rt_hal_worker_complete`

## The absent symbols

Verified by repo-wide grep over `src/` — **zero files** define any of these:

| symbol | files defining it in `src/` |
|---|---|
| `rt_hal_env_access_marked_plan` | 0 |
| `rt_hal_exact_exit_arena_install_or_fail` | 0 |
| `RtHalExitCapture` | 0 |
| `rt_hal_exit_type_descriptor_v2` | 0 |

## Interpretation

This is either a large undocumented removal, or the described feature surface
was never implemented under these names. The spec is detailed and internally
consistent, which favours "planned/removed" over "invented" — but nothing in
`src/` corroborates it either way, so the history needs an owner's eye.

## Unblock condition

Establish which it is. If the surface was removed, either restore it or retire
the spec deliberately with a record. If it was never built, the spec is a
design document ahead of its implementation and should say so in its docstring
until the surface lands. Do not weaken the assertions to make the file green.

## Provenance note

Filed twice: wave 16C created this record and it disappeared from the working
tree before commit — untracked files in this shared checkout are periodically
swept by peer sessions. Re-derived from the spec's own `# NOTE:` block, with
the four-symbol absence re-verified independently, and committed alongside the
spec.
