# SSpec-Maintain Lane-Aware Scoring

Recognition of lane-gated specs in scoring metrics to prevent SKIP-clean lanes from scoring as missing coverage.

## Resolved 2026-09-06

Implemented in `src/app/sspec_maintain/source_facts.spl`. A `skip(...)` reached
only through a conditional probe branch (`if` / `elif` / `else:`) inside a
scenario is a lane-gated outcome and no longer sets the scenario's `pending`
flag, so `SSDOC-ORA-001` ("**unconditional** pending or fail-fast scaffold
remains") stops firing on SKIP-clean lane specs. Every other marker
(`pass_todo`, `pending`, `fail("todo:`) still flags wherever it sits, an
unguarded `skip(...)` at the scenario body's own indent still flags, and a
gated scenario carrying no real assertion still fails ORA-001 on
`real_assertion_count == 0` — so the exemption cannot be used to hide a
scaffold.

Measured on `test/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.spl`
(`simple run src/app/sspec_maintain/main.spl scan <path> --no-cache`):
49/100 with 1 blocker (`SSDOC-ORA-001`) before, 84/100 with 0 blockers after.
`test/02_integration/app/tools/notebook/cuda_exec_spec.spl` is unchanged at
93/100, 0 blockers.

Proof: `test/01_unit/app/sspec_maintain/pending_detection_spec.spl` —
"keeps a probe-guarded skip( out of the unconditional-scaffold blocker" and
"still flags an unguarded skip( at the scenario body's own level".

Scope note: the record's cited design section
`doc/05_design/app/tools/notebook_lanes_architecture.md` § Lane-gated specs
does not exist — that document has no such section, and `%%mode` is a notebook
CELL magic (`src/lib/nogc_sync_mut/notebook/magics.spl`), not a `.spl` spec
construct. The penalty that actually reproduced is the one above: environment
and lane probe guards written with `skip(...)`.
