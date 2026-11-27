# testrun2 — Whole-Surface Test Health Results (2026-11-11)

Scope: every test surface outside testrun1's test/01_unit + test/02_integration.
Host: Windows, tracked seed binary `bin/simple.exe` (Simple v1.0.0-rc.1),
interpreter mode, `--no-cache`, SIMPLE_TIMEOUT_SECONDS=300.
Worktree: `simple-testrun2-20261111` @ `work/testrun2-20261111` (base c6e52eec35614).
Ledger: `build/review/testrun2-ledger.tsv` (also copied to the main checkout).

## Verdict totals (4649 item rows)

| verdict | count |
|---|---|
| PASS | 823 |
| FAIL (routed, causes in ledger) | 219 |
| ROUTED (by-design / non-spec surfaces) | 151 |
| NOT_REACHED (timebox / crash tails) | 3456 |

## Per-surface counts (enumerated / ran / passed / fixed / routed / not-reached)

| surface | enum | ran | pass | fixed | fail-routed | not-reached |
|---|---|---|---|---|---|---|
| test/00_formal_verification | 34 | 34 | 32 | 8 | 2 | 0 |
| test/00_quick | 1 | 1 | 0 | 0 | 1 (deliberate-red probe, verified matches bug doc) | 0 |
| test/04_smoke | 8 | 8 | 8 | 0 | 0 | 0 |
| test/07_security | 2 | 2 | 2 | 0 | 0 | 0 |
| test/09_baselines (probe) | 1 | 1 | 1 | 0 | 0 | 0 |
| test/smoke (hello) | 1 | 1 | 1 | 0 | 0 | 0 |
| test/shared | 21 | 21 | 21 | 0 | 0 | 0 |
| test/cert | 84 | 84 | 0 | 0 | 84 | 0 |
| test/fixtures | 63 | 50 | 0 | 0 | 63 | 13 |
| test scratch (tmp_repro/zz/_probe) | 6 | 6 | 3 | 0 | 3 | 0 |
| colocated src specs (src/lib,compiler,os,app) | 203 | 182 | 145 | 0 | 37 | 21 |
| colocated examples specs (incl. ERP + obsidian) | 62 | 62 | 52 | 33 | 10 | 0 |
| test/03_system | 4148 | 713 | 547 | 0 | 166 | 3435 |
| test/system | 1638 | 0 | 0 | 0 | 0 | 1638 |
| test/feature | 352 | 0 | 0 | 0 | 0 | 352 |
| test/05_perf | 201 | 0 | 0 | 0 | 0 | 201 |
| test/perf | 73 | 0 | 0 | 0 | 0 | 73 |
| md sdoctest lane (13 groups, 1049 blocks) | 13 | 13 | 11 groups | 0 | 2 groups (27 block fails) | 0 |
| spl comment-doctest lane (src/lib, src/compiler) | 2 | 0 | 0 | 0 | 2 | 0 |

test/08_web and test/11_* do not exist in this checkout (0 files).

## Fix commits (one per root cause)

1. `6089763cc3f6d` fix(verification-stdlib): expose fns used across
   compiler_rust std modules — 10 `pub` marks in
   `src/compiler_rust/lib/std/src/verification/**` (cross-module private-fn
   calls rejected by 2026-11-09 visibility enforcement). Fixed 8 formal specs
   (lean_workflow, unsupported_construct, regeneration,
   regeneration_theorem_emission_class, deterministic_emission, lean_codegen +
   foundations for lean_block_integration/tool_checker).
2. `3822924613bb1` fix(formal-specs): disambiguate co-compiled duplicate type
   imports — explicit `use` of `CheckResult` (checker.spl vs seed-stdlib
   verification_checker.spl) and `LeanTheorem`/`LeanCodegen{,Options}` from
   `verification.lean.codegen` (package-root import was ambiguous between
   contracts.spl and _Codegen/lean_codegen.spl shapes). Fixed tool_checker +
   lean_block_integration (11/11, 10/10 verified).
3. `c7accb772625a` fix(simple-erp): expose helper fns imported by ubs_test
   specs — 23 `pub` marks across 13 ERP modules. Verified 21/21 green.
4. `207520ebb6667` fix(obsidian-search): expose helpers imported by test specs
   (15 files, mechanically derived from spec use-lists) + add mandatory
   `# @cover` admission annotations to `test/system/obsidian_search_spec.spl`
   (their absence aborted the whole test/ dir run). System spec 13/13; unit
   dir 158/166.

## Failure families routed (not fixed)

- **spec-impl API drift**: `src/app/interpreter/**` colocated specs (12 files)
  reference statics/behavior absent from current interpreter sources
  (ActorHeap/SchedulerConfig/PersistentVec/Lazy/BinaryRef `new/default/small`,
  plus 2 internal parse errors). Needs interpreter owner.
- **missing impl**: `src/app/ffi_gen{,. specs}/module_gen_spec.spl` import
  `app.ffi_gen.types` which does not exist (orphaned specs).
- **not-a-spec over-collects**: `sspec_*.spl` source modules and
  zero-example/`declares only names` files matched by the spec glob.
- **cert corpus**: 84 `fn main()` + expected-stdout programs; runnable via
  `scripts/check/cert/run-tool-qual-corpus.shs` with the self-hosted binary,
  not seed BDD.
- **fixture harness**: test/fixtures specs run under parent harnesses
  (deliberate red/zero/crash fixtures); standalone chunk runs hang on watchdog.
- **behavioral**: three_payload_compile_refinement (refinement flag drift),
  build_cache_parse_reuse (fixture seed-parser reject + 0xC00000FD child stack
  overflow under --parallel), sspec_preparation, riscv_common_alu, mailbox,
  persistent_dict.
- **env/extern**: fpga_linux lane, lint_spec (BinaryReader extern),
  linker enum re-registration.
- **examples tooling suites**: ghost_spec hits a seed parser gap
  (`Unexpected token: expected New...`); mcpgdb/mate_broker/llm_cli_tools/
  deeplearning suites fail to compile under seed (per-spec causes not isolated
  in shared chunk logs); obsidian integration specs failed pre-fix on the same
  `js` visibility already fixed in commit 4 (re-run not reached).
- **parallel-mode flake**: obsidian analytics_spec fails 8/8 under
  `--parallel` but passes 12/12 solo (shared in-memory state across workers).
- **md-lane visibility**: 27 fenced-block failures in doc/07_guide (26) +
  examples/10_tooling (1) — snippets import `std.nogc_async_mut.async_sffi
  .waker_signal` and `std.spec.mock.mock_policy_init_hal_only`, both private.
  One-line `pub` fixes identified, not applied (no-verify rule under resume).
- **runner empty-lane bug**: lanes with zero blocks report
  `SDoctest Results: 0 total, 0 passed, 1 failed`, flipping `test <dir>`
  exit code to 1 despite all specs green (seen in ERP/obsidian/security runs).

## Surfaces not reached (timebox)

test/03_system tail (3435), test/system (1638), test/feature (352),
test/05_perf (201), test/perf (73); spl comment-doctest per-file lane
(dir-scoped `--spl-doctest` degenerated into a recursive spec run and
watchdog-crashed; the proper per-file lane needs its own session).
The seed interpreter costs ~5–15s/spec; full 03_system alone projects
~4–6h at ≤8 workers.

## Notes for follow-up

- 4 wm_compare goldens were assume-unchanged before the sweep (restored state
  preserved; no golden was touched).
- doc/08_tracking/test/test_db.sdn* and test_result.md were mutated by runs
  and restored; never staged.
- Untracked files NOT from this lane were left alone in the worktree:
  `.capsule-receipt`, `doc/09_report/cuda_generated_2d_readback_2026-11-11.md`,
  `doc/09_report/macos_vulkan_web_live_evidence_2026-11-11.md`,
  `doc/09_report/metal_generated_2d_readback_2026-11-11.md` (another agent's
  evidence artifacts).
