# Collection planner acceptance manual

Status: **authored inventory; not generated or runtime verified** (2026-10-03).
Executable: `test/03_system/app/compiler/feature/collection_planner_spec.spl`.
Full acceptance: `doc/03_plan/sys_test/collection_planner.md`, CP-001-A through
CP-011-C. Requirements: `doc/02_requirements/feature/collection_planner.md`;
NFRs: `doc/02_requirements/nfr/collection_planner.md`.

This manual distinguishes a real selector/explanation integration slice from
the full typed-collection/compiler/runtime feature. No passing test or generated
manual is claimed. Six authored scenarios call `collection_plan_select` and
`collection_plan_explain`; none execute selected MIR or an indexed collection.

| Executable scenario | Fixture | Observable contract |
|---|---|---|
| CP-GUARD-01 | static size 100, hard bound 2, admitted p95 2 | Original, no admitted decision evidence, `contradictory-size-bound` and original fallback explained |
| CP-GUARD-02 | static size 2, hard bound 2, admitted p95 3 | Original; contradiction explained; all alternatives not evaluated |
| CP-GUARD-03 | static size 2, hard bound 2, three lookups | Linear; static evidence and small/quiet reason |
| CP-GUARD-04 | same static fixture, unadmitted p95 size 1000/lookups 10000 | Linear from static facts; profile values rendered unknown |
| CP-GUARD-05 | explicit hash with unstable mutation epoch | Original; semantic proof failure visible for hash |
| CP-GUARD-06 | admitted probes 100/collisions 40, ordered capability | Ordered; hash collision rejection; memory still unproven/not modeled |

Each scenario visibly prepares typed collection facts and inspects the selected
collection plan. The two other reserved flows (compile the same program in each
engine; compare results and operation counts) are intentionally absent until
real production execution helpers exist. Their absence blocks full acceptance.

REQ-009/010/011 are only partially addressed by the six guards. The full 33-case
plan requires typed/missing-value semantics, five-engine parity, registry and
cache identity, stable indexed algorithms, generic collision behavior, typed
diagnostics, logical DAG validation, fusion effects/error traces, all join
duplicate/order policies, memory caps and actual selected-plan execution.

Admit only a pure-Simple self-hosted runtime and runner that executes `it`
bodies. Capture real baseline RED and candidate GREEN before claiming TDD.
The available seed is not acceptable evidence. No runtime was available when
this inventory was authored; no command result is fabricated here.

For full acceptance, retain exact outputs, callback traces, artifact and receipt
identities and actual operation counters. The scaling fixture sizes are 1000,
2000, 4000, 8000 with endpoint exponent at most 1.15; all-equal output work is
separate. Five warm runs per case must meet the selected 10% wall-time, 20% RSS
and 5% startup/request regression limits against same-revision baselines.
Missing measurements remain missing, never PASS.

After an admitted runner exists, generate this manual from the executable with
`simple spipe-docgen <spec> --output doc/06_spec --no-index`, inspect the rendered
steps and requirement traceability, and retain the generator result. Until then
this file remains an authored companion and cannot satisfy generated-manual
verification or release admission.
