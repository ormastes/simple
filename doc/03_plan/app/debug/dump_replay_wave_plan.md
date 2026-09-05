# Dump / Replay Wave Plan (this repo's slice)

**Date:** 2026-09-05 · **Design:** `doc/05_design/app/debug/debug_capability_truth_wave0_design.md` · **State:** `.spipe/debug_capability_truth_wave0/state.md`
**Source plan:** `doc/01_research/infra/dump_replay/simple_dump_replay_fw_spipe_devhub_design_plan_2026-09-05.md` §17 (Waves 0–11), §21 (first slice), §22 (paths)

This maps the addendum's 12 waves onto what this tree can honestly do. Only Wave 0 is active. Every later
wave lists its **entry condition**; a wave with an unmet entry condition is not started, and no capability
it would deliver is labelled above `Unverified`.

## Wave 0 — capability truth + contract lock (ACTIVE)

| # | step | lane | done when |
|---|---|---|---|
| 0.1 | `StateCapabilityReceiptV1` + `CapabilityStatus` + validator + conformance spec + guide | W2 | spec GREEN on seed; guide has "Producer (does not exist yet)" |
| 0.2 | Reader reconciliation: define `_record_outcome`, `_session_count`; fix policy-ctor imports; resolve `receipt_id`; 2 specs | W3 | `evidence_inspect_v1_spec.spl` + contract happy path GREEN on seed |
| 0.3 | Bug record for `_apply_probe`, `_authorize_at`, `_record_at`, `DebugProbeKindV1`, `.Probe` (non-compiling callers) | W3 | record lists each with file:line |
| 0.4 | Verify seven §4.2 relabels against source; record CONFIRMED/REFUTED/PARTIAL | W4 | bug record per row with decisive function |
| 0.5 | Relabel `doc/07_guide/app/tools/sreplay.md` + help strings to the agreed label | W4 | grep before/after counts recorded |
| 0.6 | Review, re-run every spec each lane reports, commit per lane, refresh `debug_profile/skill.md` | Fable | commits on `work/debug-perf-dump-skills-2026-09-05` |

## Later waves — entry conditions

| wave | addendum deliverable | entry condition in this tree | current status |
|---|---|---|---|
| 1 | strict-off compiler proof (`release-minimal\|symbolized\|fault-capsule\|probeable`) | a deployable self-hosted `bin/simple` on this host | BLOCKED — bootstrap-only binary |
| 2 | import/normalization: ELF core, minidump, Mach-O, firmware capsule, T32 importer; **bundle writer** | Wave 0 GREEN (0.1 + 0.2) | not started — writer admissible after 0.2 |
| 3 | interpreter checkpoint/resume | Wave 2 writer emits a bundle the reader accepts | not started |
| 4 | interpreter replay/reverse/fork | Wave 3 + event log with `deterministic` measured, not hard-coded (`evidence_replay_v1.spl:135`) | not started |
| 5 | one firmware fault capsule (Cortex-M or RV32) | RV32 VM snapshot relabel resolved (0.4) + Wave 2 capsule importer | not started |
| 6 | minimal machine plane + SimpleEMU slice | live `AddressMap`/`SfrBus`/`MachineGraph` (hardware plan) | not started |
| 7 | TRACE32 capture/viewer/sim split | T32 MCP host available; `.claude/skills/lib/t32.md` | not started |
| 8 | native adapters (rr, GDB record, CRIU, TTD) | Wave 2 | not started |
| 9 | CPU/GPU/framegraph profiling | `perf` regression gate GREEN (`perf_regression_tests_4_mechanisms_red_2026-09-05.md`) | BLOCKED |
| 10 | RTL/ISA differential | Wave 5 + RISC-V formal dual-track gate | not started |
| 11 | Skill Foundry curriculum ("ten mixed dump cases") | Waves 2–3 produce real bundles; `.spipe/training/splits.sdn` (sibling plan) | not started |

## Rules carried from the addendum
- No `Supported` without a runnable acceptance receipt; default `Unverified`.
- Core/fault dump is analysis-only unless complete restore state is demonstrated.
- Reverse execution requires checkpoint restore + deterministic forward replay or a complete undo log.
- Assertion bypass is a tainted counterfactual fork, never a repair.
