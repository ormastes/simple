# Feature: Stage 4 self-host bootstrap

## Raw Request

`$sp_dev complete stage4_spdev.md`

## Task Type

bug

## Refined Goal

Produce, admit, sanity-check, and deploy the pure-Simple x86_64 Stage 4 full CLI described by `doc/03_plan/infra/agent_sessions/stage4_spdev.md` without stub fallback, then retain the required evidence and handoff rows.

## Acceptance Criteria

- AC-1: Every newly discovered blocker is claimed in `bug_db.sdn` before its pure-Simple owner is edited, and the exact pre-fix failure is retained.
- AC-2: The current `i1`-to-pointer LLVM failure is fixed in the pure-Simple MIR-to-LLVM owner without weakening `llc` verification or substituting a zero value.
- AC-3: Regression evidence covers the exact `i1`-to-pointer conversion and adjacent pointer/integer conversion directions, including boolean-value preservation.
- AC-4: The failed `env/paths.spl` pure shard emits verifier-valid LLVM and completes with `SIMPLE_NO_STUB_FALLBACK=1`.
- AC-5: One admitted current-source Stage 3 rebuild passes identity and sanity gates, with executable hash and resource receipt retained.
- AC-6: One true Stage 4 run sets `SIMPLE_BOOTSTRAP_STAGE4=1`, uses full-resource incremental mode and progress logs, compiles the full CLI, and produces no failed-file or stub-fallback markers.
- AC-7: The exact fresh Stage 4 binary passes CLI sanity and `check-bootstrap-essential-tools-smoke.shs`, including test-runner, lint, duplicate-check, and aggregate PASS markers.
- AC-8: The canonical bootstrap wrapper deploys the admitted binary with provenance and rollback gates, and the installed binary matches the accepted artifact.
- AC-9: `stage4_spdev.md`, bug records, and applicable process/guide evidence are current; `doc/06_spec` contains zero executable `*_spec.spl` files; direct-env/runtime guards pass.
- AC-10: x86_64 remains first priority; post-x86 host/CPU rows stay active with their recorded prerequisites and are not misreported as complete.

## Scope Exclusions

No Rust-seed workaround, verifier relaxation, source-import workaround, ARM/RISC-V bootstrap execution before x86 acceptance, or release/version tag.

## Cooperative Review

- Root-cause sidecar: inspect LLVM cast legality and shared lowering owners without editing.
- Regression sidecar: review exact and adjacent test coverage using shared helper name `emit_bitcast_ir` and fail-fast assertions.
- Merge owner and final highest-capability reviewer: `/root`.
- Production helper under consideration: `emit_legal_bitcast_conversion`; no helper is accepted until the root review proves the smallest owner.
- Scenario-manual flow and generated-manual review: N/A because these are compiler unit regressions, not operator-facing SSpec scenarios.

## Phase

dev-done

## Log

- dev: Restored the missing state file with 10 acceptance criteria and x86-first cooperative review ownership.
- dev: Pushed LLVM cast hardening, staged-native SSA store retention, and 181s-to-2.70s authority fingerprint batching.
- dev: Admitted current pure-Simple Stage 3 at aa0586ed281ae271b6254b8c21e3e0d847639dbdf644e7bef6c5ec07e1a43cf6.
- dev: True Stage 4 completed 2,116 source loads and 1,431 surfaces, then isolated one Array-to-Named HIR routing defect; three candidate cycles stayed red, so the mandatory session cap stopped further edits. No Stage 4 binary or deploy exists.
