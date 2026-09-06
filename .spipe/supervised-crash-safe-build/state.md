# Supervised / Crash-Safe Build

## Status: ACTIVE — opened 2026-08-17

Multi-agent lane. This file is the recovery anchor: today three sessions died and
`.spipe/` state was the ONLY artifact that survived (scratchpad notes were absent
on recovery for the enterprise and office lanes). If you are picking this up cold,
everything you need is below.

## Type
compiler / driver — reliability

## Goal
A native build must reach the **END** of the source list even when a compile unit
DIES, and must classify every unit into one of six disjoint outcomes:
`OK / ERROR / CRASHED / TERMINATED / TIMEOUT / NOT_RUN`.

Today a worker's death is the parent's death: one segfaulting module aborts the
whole build, the remaining modules are never attempted, and the operator learns
about exactly one defect per multi-hour bootstrap cycle. That serialization is
currently the dominant cost of every bootstrap defect (severity P1).

## Canonical documents
- Requirement (authoritative, read first):
  `doc/02_requirements/compiler/supervised_builder.md` (filed 2026-08-17, R1..R8
  + the six-module acceptance fixture).
- Feature wiki: `doc/00_llm_process/feature_expert/supervised_build/skill.md`
- Layer wiki: `doc/00_llm_process/layer_expert/compiler_driver/skill.md`

## Design decision (from the user — do not relitigate)
Unstable mode = **per-unit SEPARATE PROCESS + run-to-end + classified outcomes**.
- It is the **DEFAULT on the BOOTSTRAP path only**, NOT for ordinary interactive
  runs.
- It is exposed as an **explicit flag** either way, so both paths can select it.
- The **session daemon is NOT the problem** and may stay for interactive use. Do
  not propose removing it as part of this feature.
- One implementation, two front ends (R8): bootstrap and ad-hoc share the
  supervisor. A bootstrap-only path would drift.

## File ownership right now (three agents in flight)
| path | state | owner |
|---|---|---|
| `src/compiler/80.driver/driver_build/build_outcome.spl` | **LANDED**, unit-verified | landed — safe to read/depend on |
| `test/01_unit/compiler/driver/build_outcome_classification_spec.spl` | **LANDED** | landed |
| `src/compiler/80.driver/driver_aot_native_output.spl` | **IN FLIGHT** — outcome accumulation | parent agent (this lane's launcher) |
| `src/compiler/80.driver/driver_build/parallel.spl` | **IN FLIGHT** — separate-process "unstable mode" | sibling agent |
| six-module poisoned fixture under `test/` | **IN FLIGHT** | sibling agent |
| `.spipe/**`, `doc/**` (this lane's docs) | this agent | docs agent |

Verified 2026-08-17 by grep: `driver_aot_native_output.spl` and `parallel.spl`
contain **zero** `BuildOutcome` / `unstable` references at the time of writing —
so nothing from those two lanes had landed yet. Re-grep before assuming progress;
do not report those as done on the strength of this table.

**Do not edit `src/**` or `test/**` from a docs lane** — two writers on the shared
working tree clobber each other, which happened three times today.

## Landed and verified
- `e89f0c6f94a` `feat(driver): shared build outcome record with six disjoint
  categories` — `src/compiler/80.driver/driver_build/build_outcome.spl` (307
  lines). Public surface:
  - `enum BuildOutcomeKind` — six disjoint variants;
  - `build_outcome_kind_label`, `build_outcome_kind_order`;
  - `build_outcome_is_unverified(kind)`, `build_outcome_is_failure(kind)`;
  - `build_outcome_signal_of_status(status)`, `build_outcome_classify_status(status,
    timed_out)` — decodes the shell `128+N` signal convention;
  - `class BuildOutcomeSet` — `count_of` / `paths_in` / `all_ok` / `verdict` /
    `summary`;
  - `build_outcome_sort_text`, `build_outcome_text_list`.
  - **`failure_count()` deliberately EXCLUDES TERMINATED and TIMEOUT.** That is
    not an oversight — see host facts below.
- Spec: `test/01_unit/compiler/driver/build_outcome_classification_spec.spl`.

Supporting commits already on main that this lane depends on:
- `5b35bff37ca` streaming parse collects every file's parse error, not the first
- `4d1aca2d799` parse progress reported per file, so a stalled file names itself
- `b4872f73454` build progress emitted to stdout (stage logs were 0 bytes)
- `fb9a33b7b9e` the requirement doc itself

## Pending
- Outcome accumulation wired through `driver_aot_native_output.spl` (the fan-out
  for uncached modules).
- Separate-process unstable mode in `ParallelBuilder`
  (`driver_build/parallel.spl` — `ParallelBuildConfig` carries `num_threads` /
  `parallel_threshold` / `deterministic` / `verbose`; what it lacks is process
  isolation and outcome classification).
- The six-module poisoned fixture + its negative control.
- Bootstrap-path default wiring and the explicit CLI flag on both front ends.
- R6 resume (re-run only non-OK units) — not started.

## Acceptance criteria (from the requirement doc, verbatim intent)
A fixture of **six** modules — one parse error, one that segfaults the compiler,
one that OOMs, one that infinite-loops into a timeout, and two clean — must, in
**ONE** run:
- [ ] AC1: emit objects for both clean modules
- [ ] AC2: report all four poisoned modules in their correct categories, **by path**
- [ ] AC3: exit non-zero
- [ ] AC4: never claim six compiled, and never fabricate an artifact
- [ ] AC5: **negative control** — with the change reverted, the fixture behaves
      *worse*. A control that fails to fail means the test is broken, not the code.

Plus the standing requirement rules:
- [ ] R1 unit isolation — a child's death kills neither parent nor sibling
- [ ] R2 wait status read **directly**, never through a pipe
- [ ] R4 fail closed at the boundary, not early
- [ ] R7 bounded concurrency, honest about the host
- [ ] R8 one supervisor, two front ends

## HOST FACTS that invalidate naive evidence (load-bearing — read before judging any run)
1. **TERMINATED (143) and TIMEOUT are UNVERIFIED, never failures.** `earlyoom` on
   this host runs with `--prefer ^(simple|...)` and is *actively* SIGTERMing
   `simple` processes. A 143 says the host killed us; it says nothing about the
   code. This is exactly why `failure_count()` excludes both.
2. **Host memory:** ~103 / 125 GB used, **zero swap**. OOM kills (137/SIGKILL) are
   routine and are also host facts, not defects in the unit that died.
3. **Never read an rc through a pipe** — `cmd | tail` yields `tail`'s status. This
   has produced false greens in this repo before; R2 encodes it as a requirement.
4. **Never accept exit 0 as a pass.** `bin/simple test <spec>` has been observed
   emitting ~1897 warning lines, zero pass/fail lines, and exiting 0. Require an
   explicit `Results:` line; otherwise the run is INCONCLUSIVE, not green. See
   `doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`.
5. **Do NOT rebuild or redeploy `bin/simple`** for this lane. It is contested by
   other lanes, and the redeploy wall is a separate multi-hour problem.
6. **A `D` line in `git status` is NOT a deletion here** — the shared index is
   stale (214 false `D`s measured today). Confirm with `[ -f "$path" ]`.
7. **`git commit -- <explicit paths>` ONLY.** Never `git add -A` / `commit -a`;
   the shared index carries other lanes' staged deletions. New files need
   `git add -N` first. Audit every commit with
   `git diff-tree -r --name-status <sha>`.
8. **Any path containing a `build/` component is silently swallowed by
   `.gitignore`** — `git add` there is a SILENT no-op. Docs go under
   `doc/0X_*/compiler/`, never `.../build/`.

## Related bugs
- `doc/08_tracking/bug/stage3_parse_stalls_at_tail_43_files_2026-08-17.md`
- `doc/08_tracking/bug/lint_timeout_hwir_zca_rows_2026-08-17.md` (superlinear lint cost)
- `doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`

## Non-goals
- Dependency-aware / partial rebuild. That needs `interface_digest_of`,
  `simple.sdn` traversal, and `SmfManifest` load-verification — all still
  uncalled. Different feature; do not fold it in here.
- Routing normal builds through the Rust seed's `native_project` pipeline. It has
  real per-module hardened cache keys, but it is only reachable via
  `SIMPLE_NATIVE_BUILD_RUST=1` or a cross-target build, so it is not a drop-in and
  using it would violate the pure-Simple-default policy.
