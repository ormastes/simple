# Feature: GPU Frontend Offload (on/off switch)

## Raw Request
"make simple support gpu optimization frontend (on/offable)" — with spipe skill,
building on the two 2026-09-01 research docs; sosix unification is a separate
agent's lane (consider, not this goal).

## Task Type
feature

## Refined Goal
Ship a typed, default-off frontend offload switch (CLI/env/config) that resolves
into the existing `CompilerOffloadProfile`, records an honest `OffloadDecision`
(demotion reason or fail-closed error), and leaves every CPU-only path unchanged;
stage the GPU/SIMD frontend waves behind the peer `parser_framework` landing.

## Acceptance Criteria
- AC-1: `resolve_frontend_offload` honors CLI > env > config > default(off); unknown text is `Err`.
- AC-2: `off` → `OffloadDecision{selected: CpuReference, fallback_reason: ""}`; no GPU/runtime init on that path.
- AC-3: `on|resident` + `allow-cpu` → `selected: CpuReference`, `fallback_reason: "parse_mode_unimplemented"` (Wave 0); `+ require-requested` → `Err(frontend_offload_required_mode_unavailable…)` and the compile fails.
- AC-4: `frontend_offload_profile` sets only `LexStructure`/`Parse` stage modes; `validate_offload_profile` passes.
- AC-5: driver emits the receipt line via `dtrace` and a `frontend_offload_*=` warm-receipt row; default compile output and `deterministic_hash` unchanged.
- AC-6: unit + integration specs green with a `Results:` line; docgen manual `0 stubs`; guide/wiki refreshed.

## Scope Exclusions
- Sosix runtime unification (async-first sosix, posix aliasing, host proxy for GPU backends) — separate agent; Wave 4 consumes its interface.
- Contracts v2, grammar generator, SIMD masks, GPU kernels, CPU work table — Waves 1+, blocked on peer `parser_framework` landing.
- Peer-dirty files: `10.frontend/treesitter/*`, `core/lexer*.spl`, `structural/parse/{contracts,dialect}.spl`, `structural_adapter/`, `spipe_docgen/*`.

## Research Summary
See `doc/01_research/compiler/parser/gpu_frontend_offload_switch_gap_2026-09-05.md`.
### Existing Code
- `src/compiler/00.common/structural_contracts/offload_profile.spl:17-60` — `OffloadMode`, `OffloadFallbackPolicy`, `OffloadDecision`, `cpu_only_profile()` (clean).
- `src/lib/nogc_async_mut/compute/exec_target.spl:47,192,265` — suggest/require precedent.
- `src/compiler/80.driver/driver_source_pipeline_parsing.spl:237-240` — `_sffi_env_get` facade use (clean file).
- `src/app/cli/native_build_warm_receipt.spl:284-287` — `frontend_*=` receipt rows.
- `src/lib/nogc_async_mut/structural/parse/runtime.spl:33-45` — `parse_request` returns `parse_mode_unimplemented` fallback for accelerated modes.
### Knowledge routes
- `knowledge_registry.sdn` has no parser_framework/offload route (gap recorded); nearest expert `feature_expert/gpu_offload_check`.
### Open Questions
- NONE

## Requirements
- REQ-1 (AC-1): pure resolver — `structural_contracts/frontend_offload_switch.spl`
- REQ-2 (AC-2/3/4): decision + profile helpers — same file
- REQ-3 (AC-5): driver/CLI wiring — `80.driver`, `app/cli`
- REQ-4 (AC-6): specs, manual, guide, wiki — `test/`, `doc/`

## Architecture
Design: `doc/05_design/compiler/frontend/gpu_frontend_offload_switch_design.md`.
Plan: `doc/03_plan/compiler/frontend/gpu_frontend_offload_plan.md`.
Agent tasks: `doc/03_plan/agent_tasks/gpu_frontend_offload.md`.

## Phase
impl-done (Wave 0); merged as PR #377 a4673923076 and PR #385 3aa737b8b54

## Unverified rows (deferred — not PASS)
| AC | What is unproven on this host | Prerequisite | Resume command |
|---|---|---|---|
| AC-3 (compile fails under require-requested) | only the pure twin + decision fn are exercised; the real `parse_all_committing_impl` gate never ran end to end | deployed self-hosted `bin/simple` (the Rust seed does not execute the pure-Simple driver) | `SIMPLE_BIN=<self-hosted> bin/simple test test/02_integration/compiler/frontend_offload_driver_spec.spl --no-session-daemon` |
| AC-5 (live `dtrace` receipt + warm-receipt row) | receipt text proven via `driver_frontend_offload_receipt_for`; not observed from a real compile | same | same, plus `SIMPLE_INTERP_TRACE=1 SIMPLE_FRONTEND_OFFLOAD=on <self-hosted> run hello.spl` |
| AC-5 (`deterministic_hash` parity off vs on+allow-cpu) | no spec compares stage hashes across the two settings | self-hosted binary running the real parse pipeline twice | `SIMPLE_FRONTEND_OFFLOAD=off` / `=on` `native-build` of one fixture; diff `StageReceipt.deterministic_hash` in the warm receipts |
| AC-5 (warm rows in a real native-build receipt) | `frontend_offload_rows` unit-tested; `_warm_frontend_identity` digest never observed with the rows | self-hosted `native-build` run | `SIMPLE_FRONTEND_OFFLOAD=on <self-hosted> native-build <fixture>` and inspect the warm identity inputs |
| AC-6 (manual accuracy) | integration manual counts the two `skip()` cases as active (docgen counts statically); manuals generated with the main-tree docgen because the committed one fails `E1002 spec_kw_line` | committed docgen fix (peer `spipe_docgen` landing) | `bin/simple spipe-docgen test/02_integration/compiler/frontend_offload_driver_spec.spl --output doc/06_spec --no-index` |
| AC-1 (`simple.sdn frontend.offload*` source) | resolver honors an injected config value (spec `uses the config value when CLI and env are absent`), but the driver forwards `""` — no `ProjectContext` in the parse pipeline | Wave 1 row GFO-005: thread `ProjectContext` (`80.driver/project.spl`) into `driver_frontend_offload_switch` | after GFO-005: `simple.sdn` with `frontend: { offload: on }`, `SIMPLE_INTERP_TRACE=1 <self-hosted> run hello.spl` → receipt `source=config` |

## Log
- 2026-09-05 intake/research/arch: saved two 2026-09-01 research docs; wrote gap research, switch design (+tldr), staged plan, agent tasks; froze vocabulary; worktree `/home/yoon/dev/simple-gpu-frontend`.
- 2026-09-05 impl A: `structural_contracts/frontend_offload_switch.spl` (126 lines) + `__init__` exports + `test/01_unit/compiler/structural/frontend_offload_switch_spec.spl` — `Results: 16 total, 16 passed, 0 failed`; sabotage (env beats cli) → `16 total, 15 passed, 1 failed`; reverted green; `direct-env-runtime-guard --working` PASS; seed binary `bin/release/aarch64-unknown-linux-gnu/simple`. Language bug filed: `doc/08_tracking/bug/auto_keyword_rejected_as_named_argument_label_2026-09-05.md` (positional construction workaround).
- 2026-09-05 impl B: driver gate in `parse_all_committing_impl` (`driver_frontend_offload_switch/decision`, pure twin `driver_frontend_offload_receipt_for`), `--frontend-offload{,-fallback}` flags in `src/app/run/main.spl` + `native_build_main.spl` (env_set only), warm-receipt rows `frontend_offload_{requested,selected,reason,source}=`. Unit spec `test/01_unit/compiler/driver/frontend_offload_driver_unit_spec.spl` `5 total, 5 passed`; sabotage (available=true) `2 failed` naming the reason assertion; reverted green. Integration probe `1 passed, 2 skipped` — seed ignores the switch (`SIMPLE_FRONTEND_OFFLOAD=on ... require-requested` still exits 0; flag path only on self-hosted binary). Audit PASS. Config source is `""` (no project-config reader in the driver; no new SDN parser). Pre-existing red: `native_build_cache_plumbing_spec` 13 failed with and without the edit.
- 2026-09-05 root: consolidated both Wave-0 `false` literals into `frontend_offload_gpu_parse_available()` (contract-owned, exported); re-ran the three specs + docgen (see next log line).
- 2026-09-05 root verify: after consolidation `frontend_offload_switch_spec` 16/16, `frontend_offload_driver_unit_spec` 5/5, `frontend_offload_driver_spec` 1 passed 2 skipped (seed); binary `bin/release/aarch64-unknown-linux-gnu/simple` unchanged across runs. Docgen: worktree's committed `spipe_docgen` fails `E1002 spec_kw_line not found`; the main tree's (peer-dirty) docgen generates all three manuals `0 stubs` under `doc/06_spec/{01_unit/compiler/{structural,driver},02_integration/compiler}/` — provenance: main-tree docgen sources, not the committed ones.
- 2026-09-05 root: replaced the Wave-0 stub fn with `val FRONTEND_OFFLOAD_GPU_PARSE_AVAILABLE: bool = false` (lint STUB002 on `-> bool: false`); re-verified 16/16, 5/5, 1+2 skipped; `bin/simple lint frontend_offload_switch.spl` → `Lint passed`; env guard PASS. Wave 0 (GFO-001..004) complete; Waves 1+ blocked on peer parser_framework landing. Not pushed (peer landing in progress).
- 2026-09-05 root (advisor finding): `auto` previously decided byte-identical to `off` (empty reason) — a silent fallback. Fixed: `auto` + allow-cpu → reason `auto_profile_not_implemented_wave_1` (`FRONTEND_OFFLOAD_AUTO_REASON`, same text as `auto_profile.spl`); `auto` + require-requested → `Err(frontend_offload_required_mode_unavailable: auto)`. Spec against the pre-fix contract: `18 total, 16 passed, 2 failed` (both new auto cases); fixed: `18/18`, driver unit `6/6`; manuals regenerated `0 stubs`; env guard PASS; workspace-root-guard: 213 pre-existing violations, 0 on lane paths. Layer-expert pointers added to `layer_expert/{compiler_driver,compiler}`.
- 2026-09-05 bug fix: seed parser now accepts `auto` as a named-argument label (`helpers.rs` label match + `is_likely_named_arg`). Rebuilt seed (`cargo build --release --bin simple`, 1m18s warm, main-tree target dir): `parser_auto_contextual_keyword_spec` 3/3 (pre-fix seed: `expected Comma, found Colon`, spec executed nothing), `parser_contextual_keyword_named_arg_spec` 8/8, `frontend_offload_switch_spec` 18/18 on the new seed. Positional workaround retained until the deployed seed carries the fix.
- 2026-09-05 Fable audit fixes: `FRONTEND_OFFLOAD_AUTO_REASON` re-exported; shared `frontend_offload_rows` now derives both the warm-receipt rows and (via the same contract) the driver receipt — canonical `requested=` encoding, errors as `frontend_offload_error=`; `run` no longer forwards the two flags to the seed (it read `--frontend-offload=on` as a file path); design/guide corrected (rows are identity-digest inputs; decision recomputed per call, receipt memoized process-wide; `frontend_offload_profile` has no Wave-0 caller); tldr `auto` lines; plan/agent-task guide path; selection receipt lists the CLI files. Disclosed: adding the rows invalidates every pre-existing warm identity once.
- 2026-09-06 recheck (Opus 5; **Fable was unavailable — its monthly spend limit was hit mid-audit**, so this pass is NOT Fable-reviewed): verified on merged `origin/main` `c972fd643da` — no positional `FrontendOffloadSwitch` construction remains anywhere in `src/` or `test/`; both `helpers.rs` sites present (label match :571 + `is_likely_named_arg` :713); `auto=true` can only co-occur with `mode=CpuReference` (set together in `parse_frontend_offload_value`), so the `switch.auto` branch ordering is safe. Two real defects found and fixed: (1) `native_build_main.spl` forwarded `--frontend-offload*` into the worker argv (`run` already stripped them) — now stripped in both; (2) the aarch64 `c_char` break was a CLASS, not one site, and a read-side cast was the wrong fix — `cuDeviceGetName(name_buf.as_mut_ptr(), …)` breaks on the **write** side too. Typed the buffer `[0 as std::os::raw::c_char; 256]` at `runtime/src/cuda_runtime.rs:1100,1555` and `gpu/src/backend/{cuda,rocm}.rs`. Proof: `cargo check -p simple-runtime --features cuda` → 2×E0308 before, `Finished` after (the runtime crate had never compiled with that feature on aarch64). `simple-gpu` cannot be compiled from this tree at all (not a workspace member) — recorded as GFO-008.
- 2026-09-06 impl of the audit's missing items: **GFO-008** — added `gpu` to the cargo workspace `members`; that alone surfaced **4 more E0308s** (`CString::as_ptr()` → `*const i8` externs at `gpu/src/backend/cuda.rs:299,489` and `rocm.rs:269,440`), i.e. `simple-gpu` had never compiled on aarch64 with its features. Retyped all five extern declarations to `c_char`; `cargo check -p simple-gpu --features cuda,rocm` rc=0, `cargo check --workspace` rc=0, seed release build rc=0. **GFO-009** — the driver now builds `frontend_offload_profile(switch)` and fails closed on `validate_offload_profile` (`frontend_offload_invalid_profile: …`), so the helper is wired rather than unused. Spec vocabulary — driver-unit and integration specs now use frozen `step()` names with outcome-phrased `it` titles (6/6 and 1 passed + 2 skipped; both manuals regenerated `0 stubs`). **GFO-005 correction**: it is NOT blocked on `parser_framework` — `DriverContext.config` never loads `simple.sdn` and `ProjectContext` has no caller in the compile path, so the real question is where to pay the config read (CLI layer, off the hot path, is the cheap option); recorded as an open follow-up with that tradeoff spelled out.
