# Feature Expert — Supervised / Crash-Safe Build

## Role

Own feature-specific process knowledge for the **supervised builder**: the native
build must reach the END of the source list even when a compile unit DIES, and
must classify every unit as `OK / ERROR / CRASHED / TERMINATED / TIMEOUT /
NOT_RUN`.

Lane state (authoritative, updated as work lands):
`.spipe/supervised-crash-safe-build/state.md`.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)
- [pipeline next step plan](../../pipeline_next_step_plan.md)

## Feature Links

- Requirements: [`doc/02_requirements/compiler/supervised_builder.md`](../../../02_requirements/compiler/supervised_builder.md)
  — R1 unit isolation, R2 classified outcomes, R3 run-to-end, R4 fail closed at
  the boundary, R5 attribution of deaths, R6 resume, R7 bounded concurrency,
  R8 one implementation / two front ends.
- Source (landed): `src/compiler/80.driver/driver_build/build_outcome.spl`
- Source (extension points, in flight):
  `src/compiler/80.driver/driver_build/parallel.spl`,
  `src/compiler/80.driver/driver_aot_native_output.spl`
- Spec (landed): `test/01_unit/compiler/driver/build_outcome_classification_spec.spl`
- Layer expert: [`layer_expert/compiler_driver`](../../layer_expert/compiler_driver/skill.md)

## Current state (2026-08-17)

**Landed and unit-verified** — `e89f0c6f94a`
`feat(driver): shared build outcome record with six disjoint categories`:
`build_outcome.spl` provides `BuildOutcomeKind` (six disjoint variants),
`BuildUnitOutcome`, `BuildOutcomeSet` (`count_of` / `paths_in` / `all_ok` /
`verdict` / `summary`), `build_outcome_classify_status` decoding the `128+N`
signal convention, and `build_outcome_is_unverified` / `build_outcome_is_failure`.

**In flight, separately owned** — do not edit these from another lane:
outcome accumulation in `driver_aot_native_output.spl`; separate-process
"unstable mode" in `driver_build/parallel.spl`; the six-module poisoned fixture
under `test/`.

**Not started:** R6 resume; the bootstrap-path default wiring plus the explicit
CLI flag on both front ends.

## Design decision (settled by the user)

Unstable mode = per-unit **separate process** + **run to end** + **classified
outcomes**. It is the DEFAULT on the **bootstrap** path only, NOT for ordinary
interactive runs, and is exposed as an explicit flag either way. The session
daemon is not the problem and may stay for interactive use.

## Implementation constraints

- **Read each child's wait status directly, never through a pipe.** `cmd | tail`
  yields `tail`'s status; that shape has produced false greens here before (R2).
- **`failure_count()` deliberately EXCLUDES `TERMINATED` and `TIMEOUT`.** Both are
  UNVERIFIED outcomes about the host, not verdicts about the unit.
- `ParallelBuilder` (`parallel.spl`) already fans out uncached modules with
  `ParallelBuildConfig` (`num_threads` / `parallel_threshold` / `deterministic` /
  `verbose`); what it lacks is process isolation and outcome classification.
- The Rust seed's `native_project` pipeline has genuine per-module hardened cache
  keys and prints `[native-incremental] N reused / M rebuilt`, but is reachable
  only via `SIMPLE_NATIVE_BUILD_RUST=1` or a cross-target build — it is **not** a
  drop-in, and routing normal builds through it would violate the
  pure-Simple-default policy.

## Host facts that invalidate naive evidence

1. `earlyoom` on this host runs `--prefer ^(simple|...)` and is actively
   SIGTERMing `simple`. **rc 143 is UNVERIFIED, never failed.**
2. ~103 / 125 GB used, **zero swap** — SIGKILL/OOM (137) is a host fact too.
3. **Never accept exit 0 as a pass**: `bin/simple test` has emitted ~1897 warning
   lines, zero pass/fail lines, and exit 0. Require an explicit `Results:` line;
   otherwise INCONCLUSIVE. See
   `doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`.
4. Do **not** rebuild or redeploy `bin/simple` for this lane.

## Verification

Acceptance is the six-module fixture (one parse error, one segfault, one OOM, one
timeout, two clean) in ONE run: objects for both clean modules; all four poisoned
modules reported in their correct categories **by path**; non-zero exit; never
claims six compiled and never fabricates an artifact. Plus a **negative control**
— with the change reverted the fixture must behave *worse*; a control that fails
to fail means the test is broken, not the code.

Landed unit coverage:
`bin/simple test test/01_unit/compiler/driver/build_outcome_classification_spec.spl`
(read the `Results:` line, not the exit code).

## Update Rule

When research, requirements, architecture, design, tests, implementation,
verification, or release artifacts for this feature change, update this file and
`.spipe/supervised-crash-safe-build/state.md` in the same commit as the work.
