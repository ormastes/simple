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

## Build-side process isolation is BLOCKED (2026-08-17, `082200ce8af`)

Established by reading code, with file:line evidence — do not retry without
clearing a precondition below.

- **Run-to-end already works.** `parallel.spl:455-462` records failures into
  `errors` and falls through; a failed dependency is a `continue` (`:414-421`);
  the only `break` is work-exhaustion (`:472`). Caller iterates all errors
  (`driver_aot_native_output.spl:690-693`). This lane's Gap "build side is
  unaddressed" was WRONG.
- **What is missing is crash CONTAINMENT only.** `parallel.spl:424` calls
  `compile_fn(...)` IN-PROCESS, so one SIGSEGV/OOM kills the whole build, and
  the classifier is only reachable from an unwired path. `build_supervised()`
  exists at `parallel.spl:680` with a signal-preserving wrapper
  (`:72-73`, SEGV→139 / TERM→143 / KILL→137) and has **zero callers**.
- **A child cannot compile one module from its source path alone.** Field
  offsets are a whole-program function: one shared `MirLowering`
  (`driver_pipeline_lowering.spl:202,255`) plus a whole-program struct-layout
  PREPASS (`:209-215,262-263`) that exists precisely because
  `resolve_field_index` otherwise defaulted to 0 — a cross-module SEGV. A
  source-only child would emit objects with WRONG FIELD OFFSETS, silently.
  Two more whole-program passes mutate `mir_modules` after lowering (async
  state machines, AOP rewrites).
- **MIR serialization does not exist.** Zero `deserialize` hits for MIR;
  `mir_serialization.spl:13` is a lossy functions-only shape;
  `FrozenStorageModuleSnapshotV1` has no serializer.
- **Rejected shortcut, recorded so nobody retries it:** passing
  `capsule_identity` on argv so a child writes a conforming
  `.capsule-receipt` would let a WRONG-OFFSET object be promoted into the cache
  as AUTHENTICATED — a green build producing a miscompiled program. Strictly
  worse than today's loud SIGSEGV.
- **Precondition to unblock, one of:** (1) a round-trippable MIR +
  storage-snapshot format WITH a reader, gated by a
  `serialize → deserialize → native_capsule_mir_identity_v1` identity test; or
  (2) source-derivable stable field ordering for imported structs — i.e. the
  still-zero-caller `interface_digest_of` (`cache/action_key.spl:199`).

Because of this, the build path now **PRINTS that unstable mode was requested
but is not active there**, rather than silently dropping the intent.

## Outcome contract is specced (2026-08-17)

`test/01_unit/compiler/driver/build_unit_outcome_from_status_contract_spec.spl`
— 19 examples, `Results: 19 total, 19 passed, 0 failed`, rc=0
(`91f4147088a`, `4213a69da10`, `f927cb0d4de`). Proven to bite by a
green→red→green sabotage (reclassifying SIGTERM as CRASHED gives
`19 total, 18 passed, 1 failed`).

**Correction to the brief, not to the code: 137 is NOT TERMINATED.**
`build_outcome.spl` classifies only SIGTERM(15) as TERMINATED; an unbudgeted
SIGKILL(137) is **CRASHED, a failure**. earlyoom sends SIGTERM, which is the
never-a-failure path; a raw SIGKILL is indistinguishable from the compiler
dying, so treating it as unverified would suppress real crashes. A
budget-killed 137 is TIMEOUT via the `timed_out` flag, not via the signal.

The artifact rule lives in the SUPERVISOR, not the classifier: `from_status`
sees only a wait status, while `build_supervised` (`parallel.spl` ~816-828)
does the `artifact_fn` + `rt_file_exists` join and substitutes status 1 with
`"exit 0 but declared artifact is missing"`.

Test-side counterpart of the same contract:
[mission_critical_robustness](../mission_critical_robustness/skill.md) and
[test_runner layer](../../layer_expert/test_runner/skill.md). Lane record:
`.spipe/unstable_test_mode/state.md`.

## Update Rule

When research, requirements, architecture, design, tests, implementation,
verification, or release artifacts for this feature change, update this file and
`.spipe/supervised-crash-safe-build/state.md` in the same commit as the work.
