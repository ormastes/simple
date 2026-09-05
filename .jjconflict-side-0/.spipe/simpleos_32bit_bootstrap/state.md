# Feature: SimpleOS 32-bit bootstrap contracts

## Raw Request
Implement host-independent 32-bit SimpleOS bootstrap/toolchain support for x86_32, arm32, and rv32 without fabricated success: target triples, ABI/linker/sysroot/tool manifest, phase1/phase2 state, and fail-closed QEMU receipt contracts. Do not claim live pass or bootstrap a host compiler. Add acceptance specs/manuals/docs/wiki/bug resume rows.

## Task Type
feature

## Refined Goal
Provide one shared, data-driven contract that validates 32-bit SimpleOS target metadata, phase lineage, manifests, and nonce-bound QEMU receipts while leaving unavailable live rows blocked.

## Acceptance Criteria
- AC-1: x86_32, ARM32, and RV32 resolve canonical target triple, ABI, linker emulation, sysroot manifest, tool manifest, and QEMU binary from one interface.
- AC-2: a receipt is accepted only when Phase 1 and Phase 2 are independently hash-bound, Phase 2 names Phase 1 as parent, no-stub mode is true, and all manifest hashes are nonzero SHA-256 values.
- AC-3: QEMU acceptance requires the correct target/QEMU tuple, a 16+ character nonce repeated in guest-entry, filesystem-exec, reap-exit-37, and final-pass markers; partial or fabricated transcripts fail.
- AC-4: contract specs cover all targets and negative phase, manifest, target, and transcript cases without starting bootstrap or QEMU.
- AC-5: executable spec and mirrored operator manual remain aligned; live rows remain BLOCKED, not skipped or passed.
- AC-6: architecture/design/requirements/plans, SimpleOS guide, feature/layer expert wiki, and Bug/Todo resume records are updated. Workflow skill/agent/command files are N/A because no workflow behavior changes.

## Scope Exclusions
Host compiler bootstrap, QEMU launch, target-native compiler convergence, release, and live PASS claims.

## Cooperative Review
N/A: the bounded contract has one implementation owner and no independent code lanes; merge owner and final reviewer are the parent/root agent.

## Phase
implementation-handoff

## Log
- dev: Created state with 6 acceptance criteria.
- impl: Added v2 profiles and fail-closed receipts plus source/manual/plan/wiki updates.
- blocked: Live execution remains open in Todo rows 834-836.
