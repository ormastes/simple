# Plan-remains acceptance lane (2026-09-05)

**Goal:** every open checkbox in an actively-worked plan gets a runnable
acceptance `it`, tagged `# @tag:in-development` so the bootstrap sweep counts
it without reddening. Interface first: the spec pins the PUBLIC FUNCTION
SIGNATURE the plan promises, before any detail implementation exists.

## Selection (last 4 weeks, incomplete, ordered fewest-remains-first)

Source: `doc/03_plan/**.md` with >=1 `- [ ]`, last non-bulk commit within 28
days. The 08-11 date on many rows is `ae55a746719` ("restore tree wiped by
6f86ff32a7d") and the 08-27/08-30 dates are `e274cd33719`/`a8244005f9b`
(worktree merges) — those are bulk commits, not authorship, and are recorded
here so the dates are not misread as activity.

| remains | done | plan |
|---|---|---|
| 1 | 10 | runtime/process_safety/plan.md |
| 1 | 3 | hardware/riscv/fpga_board_bringup_jtag_10min_plan_2026-07-24.md |
| 1 | 5 | compiler/dependency_analysis/plan.md |
| 1 | 9 | agent_tasks/engine2d_four_backend_capture.md |
| 3 | 17 | sys_test/compiler_loader_script_crosslang_perf.md |
| 3 | 11 | agent_tasks/parent_authoritative_actor_process.md |
| 3 | 15 | compiler/startup_performance/startup_perf_plan_2026-08-17.md |
| 4 | 0 | os/multiarch_qemu_systest/aarch64_darwin_contract_snippet.md |
| 4 | 17 | language/gpu_fpga/sycl_parity_unified_kernel_plan_2026-06-13.md |
| 5 | 0 | app/office/excel_to_math_lib_migration.md |
| 5 | 0 | compiler/jit/compiler_jit_rendering_loops.md |
| 5 | 3 | ui/perf/render_perf_redesign_plan_2026-08-06.md |
| 6 | 0 | lib/crypto/rsa_modexp_montgomery_barrett.md |
| 6 | 1 | app/office/excel_to_math_synthesis.md |
| 6 | 2 | lib/gpu_containers_unified/unified_compute_stdlib_rollout_2026-06-16.md |
| 7 | 0 | lib/scilib/ports/scilib_port_ml.md |
| 7 | 0 | lib/scilib/ports/scilib_port_ndarray.md |
| 7 | 0 | sspec_modernization_plan.md |
| 8 | 0 | os/driver/driver_framework_module_level_sugar.md |
| 8 | 0 | agent_tasks/evidence_showcase.md |
| 9 | 0 | app/editor/editor_markdown_editing_subsystem.md |
| 10 | 0 | lib/scilib/ports/scilib_port_lapack.md |
| 10 | 0 | sys_test/cuda_host_validation_2026-07-11.md |
| 10 | 0 | agent_tasks/fat32_atomic_replace_recovery.md |
| 11 | 0 | lib/scilib/ports/scilib_port_cuda_fortran.md |
| 11 | 0 | lib/scilib/ports/scilib_port_math_block.md |
| 12 | 0 | agent_tasks/office_cli_tui_ui_access.md |
| 12 | 0 | app/mcp/mcp_startup_perf_small_tasks_2026-06-12.md |
| 16 | 0 | os/simpleos/hw_qemu/clang_board_bringup_x86_64_uefi.md |
| 16 | 5 | infra/audit/serial_sigsegv_and_test_hardening.md |
| 18 | 0 | lib/scilib/ports/scilib_port_blas.md |
| 28 | 0 | agent_tasks/simpleos_production_master_plan_completion_status.md |
| 40 | 11 | compiler/aspect_dynload/aspect_dynload_lane_plan_2026-08-19.md |
| 44 | 23 | app/simpleos/simpleos_nodejs_ai_cli_migration.md |
| 51 | 141 | compiler/sffi/sffi_universal_admission_next_2026-08-25.md |
| 75 | 0 | infra/perf_umbrella/perf_checklists.md |

## Prerequisite — DONE

`@tag:in-development` was authored at `970920e02cd` and never reached main
(the `e274cd33719` merge took the three specs but not
`src/lib/nogc_sync_mut/spec/in_development.spl` nor the runner wiring).
Restored 2026-09-05; `test/01_unit/lib/spec/in_development_tag_spec.spl`
is 21/21 green. Semantics: `doc/05_design/app/testing/in_development_tag.md`.

## Spec contract every agent in this lane follows

One file per plan: `test/03_system/plan_acceptance/<slug>_spec.spl`, where
`<slug>` is the plan's basename without `.md` and without a trailing date.

```
"""
## Purpose and audience
Acceptance oracles for the open remains of doc/03_plan/<path>.md.
## Operator workflow
bin/simple test test/03_system/plan_acceptance/<slug>_spec.spl
## Compatibility and limitations
Tagged in-development: these pin the promised INTERFACE and fail until the
plan's remaining checkboxes are implemented.
"""
# @tag:in-development
# doc-path: doc/03_plan/<path>.md
```

Rules:
- **One `it` per open `- [ ]`**, its name quoting the checkbox text so the
  mapping back to the plan is mechanical.
- **Interface before detail (goal item 4).** Each `it` calls the public
  function the plan promises and asserts its SIGNATURE and contract — return
  type, error shape, boundary values. If the function does not exist yet,
  call it anyway: an unresolved symbol is a load failure, which the tag
  neutralises, and it becomes the forcing function for the interface.
- **Real oracles only.** Every `expect()` compares a computed value against a
  named expected constant. Never `expect(x).to_equal(x)`, never a tautology,
  never `pending()`/`skip()` — the tag is the channel for "not done yet".
- No inheritance; generics use `<>`; `.spl` only.
- Do NOT edit the plan's checkboxes. Ticking a box is the implementation
  lane's job, not this one's.

## Score bar: modern sspec >= 90 (added 2026-09-05, mid-lane)

Every spec in this lane must reach a modern-sspec documentization score of
**90 or higher**. The gate default in
`src/app/test_runner_new/sspec_score_gate.spl` is 80; 90 is this lane's bar.
Authority is the scorer itself — `src/app/sspec_maintain/rules.spl` (rules)
and `score.spl` (aggregation, `effective_aggregate`) — not this prose.

Shape that carries the score: docstring header with Purpose and audience /
Operator workflow / Compatibility and limitations; `# @cover <path> <pct>`
per source file under test; a `step("...")` per phase inside every `it`;
`# oracle:` comments naming the expected constant and its provenance.
`# @tag:in-development` stays.

Never raise a score by deleting assertions. A spec that cannot reach 90 is
reported with its score and the rule ids that cost it.

**Measurement is currently BLOCKED on this host and the bar is therefore
unverified.** `simple sspec-maintain scan <path> --min-score 90` needs a
full-CLI binary, and none is deployed here; the Rust seed cannot parse the
scorer (see
`doc/08_tracking/bug/rust_seed_parser_behind_main_grammar_blocks_simple_test_2026-09-05.md`)
and `native-build` of it fails with `unresolved type: Id` in
`src/std/common/search/{ranking,types}.spl`. Until one of those is fixed, a
claimed score is a claim, not a measurement, and must be written as one.
