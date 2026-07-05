# Simple Compiler — Safety-Critical Certification Roadmap

Tracks progress toward the certification **grades** defined in `.claude/skills/cert_grade.md`
(aero / auto / space / military). Run `/cert_grade --gap` for a live assessment.
This doc is the persistent home for the **deferred time-consuming task queue**
(`.claude/skills/lib/cert_grade_infra.md`) — status + owners.

## Target grades

| Grade | Standard / level | Status | Nearest blocker |
|---|---|---|---|
| `aero-d` / `auto-a` | DO-178C DAL D / ISO 26262 ASIL A (statement cov + robustness) | **nearest achievable** | traceability matrix, robustness suite breadth |
| `aero-c` / `auto-b` | statement/branch coverage | pending | decision coverage instrumentation |
| `aero-a` / `auto-d` / `space-a` | MC/DC + tool qualification | **blocked** | stage4 wall (miscompilation) → then MC/DC infra |
| `mil-hw` (DO-254) | RTL/VHDL formal evidence | partial | RVFI/SymbiYosys full harness |

## Root ordering constraint

The **stage4 tag/box wall** (seed cranelift `BoxInt` mangles enum heap-handles through
ANY-erased channels — `codegen/instr/mod.rs:1305`) is the root certification blocker:
a miscompiling backend fails Phase-4 (optimization-soundness) and Phase-7 (tool
qualification) **by construction**. Fix the wall first; then coverage/fuzz/sanitizer
evidence becomes trustworthy. Pure-Simple codegen is already clean (deployed `bin/simple`
passes all soundness repros) — the wall is seed-specific.

## Deferred task queue (time-consuming — run detached / cron)

| # | Task | Owner | Trigger | Status |
|---|---|---|---|---|
| C1 | MC/DC instrumentation + report | codegen | after wall fix | **blocked (wall)** |
| C2 | Full optimization-soundness sweep (interp×cranelift×llvm × O0/O2) | verify | nightly cron | scaffold (redeploy_gate.sh) |
| C3 | csmith-style differential fuzzer | verify | nightly cron (time-boxed) | queued |
| C4 | Sanitizer matrix (ASan/UBSan/TSan/MSan) of seed + C runtime | infra | nightly cron | queued |
| C5 | Bidirectional traceability generator + orphan report | docs | every test run | queued |
| C6 | WCET / timing analysis | infra | on-demand (real-time claims) | not-scheduled |
| C7 | Tool-qualification validation suite (ACATS/torture analog) | verify | after wall fix | queued |

## Landed (cert-relevant this initiative)

- **Determinism / reproducibility (Phase 5):** bootstrap entry-shim filename made deterministic
  (`238d86c`) — build-twice sha256 matches. Mechanism-proven.
- **Formal (Phase 6, partial):** 27 zero-sorry Lean projects; RVFI readiness script exists.
- **Struct-registry hardening:** `SymbolId`→`SymbolName`, `Symbol`→`DepSymbol` collisions removed
  (10a1f70, 0b2b26fa) — removes a value-corruption vector (traceability/robustness relevant).

## Next actions

1. Fix the stage4 wall (`BoxInt` heap-handle tag-awareness) — unblocks C1, C7, and Phase-4/7.
2. Stand up C5 (traceability generator) — cheap, high cert value, not wall-blocked.
3. Wire C2/C3/C4 as nightly cron under `scripts/check/cert/`.
