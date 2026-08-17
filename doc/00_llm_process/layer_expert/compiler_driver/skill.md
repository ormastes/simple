# Compiler Driver Layer Expert

Mission-critical V2 bootstrap/admission status is owned by
`doc/03_plan/sys_test/mission_critical_infra_hardening_v2.md`; its active owner
failure is `doc/08_tracking/bug/stage3_selfhost_exit_139_2026-08-14.md`.

## Role

Own source discovery, import closure, phase orchestration, execution-mode
selection, and compiler-driver performance under `src/compiler/80.driver/`.

## Source-loading invariant

- `Check` mode loads only the requested checking scope.
- `Interpret` mode keeps the explicit entry bounded and lets the interpreter
  module loader resolve imports lazily.
- Native entry-closure mode loads the transitive closure selected by
  `SIMPLE_NATIVE_BUILD_ENTRY` and suppresses whole-project bulk loading.
- Other project compilation modes may bulk-load the self-hosted compiler roots
  where their global compilation model requires it.

Do not reuse the native-only entry-closure environment flag as a shortcut for
interpretation: downstream HIR/MIR branches attach native/bootstrap semantics
to it. Keep the interpret exclusion explicit in
`driver_source_pipeline_loading.spl`.

Native-project import ownership is fail-closed for duplicate bare providers.
Pure-Simple filesystem families name `std.nogc_sync_mut.platform` or
`std.nogc_async_mut.platform` directly; `src.std.platform` remains an
interpreter compatibility shim and must not force native-project to guess an
owner through a transitive alias chain. Exact and duplicate-provider controls
live in `pipeline/native_project/tests.rs` and are tracked by
`native_project_src_std_platform_alias_owner_loss_2026_08_03.md`.

## Performance evidence

The compiler-loader negative-cache and packed-byte performance handoff lives at
`doc/03_plan/sys_test/compiler_loader_script_crosslang_perf.md` (plan content
accepted; operational reconciliation pending; feature verification blocked).
Preserve its
distinction between facade failed-existence probes and filesystem syscalls, its
caller-sensitive cache key and reset generation, and its admitted-self-hosted
evidence rule. Live feature verification remains blocked by two distinct
prerequisites: the older deployed candidate's wrapper/help admission segfault,
and historical lane-A Stage3 context corruption after a clean 603-file parse.
Fresh r3 remains unproved: its first process was intentionally stopped before
Stage 2 admission so review corrections could be source-frozen; partial output
is not authority and no verdict/cycle was consumed. The latter is tracked at
`doc/08_tracking/bug/build11_stage3_compile_context_corruption_2026-08-14.md`.

For a one-file interpreted entry, measure wall time and max RSS through the
normal `bin/simple` command. A run that never reaches user code is source-loader
cost, not workload cost. Preserve the normal CPU guard; raising it is diagnostic
only and cannot be passing evidence.

Focused contract:
`test/01_unit/compiler/driver/interpret_lazy_project_sources_spec.spl`.
MCP end-to-end witness:
`test/02_integration/app/mcp_stdio_integration_spec.spl`.

Typed-storage native codegen freezes deep-copied module-qualified evidence
before cache lookup. The parent then creates class-handle MIR+storage capsules;
the builder callback sees only the frozen batch and module name. Revalidate
complete MIR/storage identity before and after codegen, bind object bytes and
size in the result receipt, and publish cache checkpoints only through the
parent completion hook. Do not call this real concurrency: the current
builder branch batches sequentially, and process workers need a complete codec.

## Separate RV64 Stage 3 MIR receiver corruption handoff (2026-08-14)

This is not the Build11 compiler-loader frontier above. The RV64 prerequisite
bootstrap reaches HIR with zero errors, then its
Stage 3 log ends in MIR method-call lowering with an impossible receiver local
ID. Inspect `method_calls_literals.spl` receiver resolution/writeback and the
`value_struct_layout.spl` push-heavy caller shapes. Do not claim the direct
`CompileContext.error_count_value` reads fixed the root cause; require an exact
native reproducer, adjacent aggregate/method-call regression, and a fresh
Stage 4 essential-tools receipt. Tracking:
`doc/08_tracking/bug/stage3_selfhost_post_hir_segfault_2026-08-14.md`.
## Restart12 bootstrap/deployment status (2026-08-14)

The current Stage 2 compiler is bootstrap-only. The static-owner receiver
frontier is repaired; a later GDB run proved the next Stage 3 exit 139 at
aggregate `HirType` transport from `maybe_copy_array_value` into
`remember_local_hir_type`. Keep that metadata owner-local and cross the helper
boundary with scalar source/destination IDs. The focused native regression is
green, but Stage 3/4 remain unadmitted, so do not advertise SPipe, deployment,
or release admission. Current owner and resume condition:
`doc/08_tracking/bug/stage3_post_file_copy_exit139_2026-08-14.md` and the
canonical deployment plan.

## Supervised / crash-safe build (80.driver, 2026-08-17)

New layer contract in `src/compiler/80.driver/driver_build/`. A native build must
reach the END of the source list even when a unit DIES, classifying each unit as
`OK / ERROR / CRASHED / TERMINATED / TIMEOUT / NOT_RUN`.

**Landed public surface** — `src/compiler/80.driver/driver_build/build_outcome.spl`
(`e89f0c6f94a`, 307 lines, unit-verified): `enum BuildOutcomeKind` (six disjoint
variants), `BuildUnitOutcome`, `class BuildOutcomeSet` (`count_of` / `paths_in` /
`all_ok` / `verdict` / `summary`), `build_outcome_classify_status(status,
timed_out)` decoding the `128+N` signal convention, plus
`build_outcome_is_unverified` / `build_outcome_is_failure` /
`build_outcome_signal_of_status` / `build_outcome_kind_label` /
`build_outcome_kind_order` / `build_outcome_sort_text` /
`build_outcome_text_list`. Spec:
`test/01_unit/compiler/driver/build_outcome_classification_spec.spl`.

**`failure_count()` deliberately EXCLUDES `TERMINATED` and `TIMEOUT`.** Do not
"fix" this. `earlyoom` on this host runs `--prefer ^(simple|...)` and actively
SIGTERMs `simple`; the host is at ~103/125 GB with zero swap. rc 143 and a
timeout are statements about the host, never verdicts about the unit — treat both
as UNVERIFIED.

**Extension points, in flight and separately owned** (re-grep before assuming any
of it landed — as of this writing both files contain zero `BuildOutcome`
references): outcome accumulation in `driver_aot_native_output.spl`, and
separate-process "unstable mode" in `driver_build/parallel.spl`. `ParallelBuilder`
already fans out uncached modules via `ParallelBuildConfig` (`num_threads` /
`parallel_threshold` / `deterministic` / `verbose`); what the layer lacks is
process isolation and outcome classification — today a worker's death is the
parent's death.

Layer rules this introduces:
- Read a child's wait status **directly**; never through a pipe (`cmd | tail`
  yields `tail`'s status — a documented false-green source here).
- Fail closed at the build boundary, not at the first dead unit.
- One supervisor, two front ends: bootstrap and ad-hoc share it. Unstable mode is
  the DEFAULT on the bootstrap path only, and an explicit flag on both.
- The session daemon is out of scope and stays for interactive use.

Requirements: `doc/02_requirements/compiler/supervised_builder.md`.
Feature expert: `../../feature_expert/supervised_build/skill.md`.
Lane state: `.spipe/supervised-crash-safe-build/state.md`.
