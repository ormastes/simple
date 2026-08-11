# Simple Compiler — Safety-Critical Certification Roadmap

Tracks progress toward the certification **grades** defined in `.claude/skills/cert_grade.md`
(aero / auto / space / military). Run `/cert_grade --gap` for a live assessment.
This doc is the persistent home for the **deferred time-consuming task queue**
(`.claude/skills/lib/cert_grade_infra.md`) — status + owners.

> Assessment date 2026-07-05. Statuses below are **evidence-backed** (file/script
> pointers + measured counts), not placeholders. Assessed against the strictest
> target (`aero-a` / DO-178C DAL A) so every gap is visible; lower grades relax
> the coverage/tool-qual objectives.

## Target grades

| Grade | Standard / level | Status | Nearest blocker |
|---|---|---|---|
| `aero-d` / `auto-a` | DO-178C DAL D / ISO 26262 ASIL A (statement cov + robustness) | **nearest achievable, gated** | traceability orphan burndown (445 down / 244 up) + Phase-0 plan docs |
| `aero-c` / `auto-b` | statement/branch coverage | pending | decision-coverage codegen instrumentation (std.mcdc is manual-only) |
| `aero-a` / `auto-d` / `space-a` | MC/DC + tool qualification | **blocked** | stage4 wall (miscompilation) -> then MC/DC codegen instrumentation |
| `mil-hw` (DO-254) | RTL/VHDL formal evidence | partial | RVFI/SymbiYosys full harness (readiness script only) |

## Phase-by-phase gap matrix (target aero-a / DO-178C DAL A)

| # | Phase | Status | Evidence (paths) | Gap | Nearest grade |
|---|---|---|---|---|---|
| 0 | Plans (PSAC/SDP/SVP/SCMP/SQAP) | **PARTIAL** | Coding/design standards declared: `.claude/rules/{language,testing,bootstrap,code-style,structure}.md`, `doc/04_architecture/**/+rule/`. No plan docs except this file under `doc/03_plan/cert/`. | Author 5 lightweight plan docs (PSAC/SDP/SVP/SCMP/SQAP equivalents). | Standards satisfy D; formal plans needed for C+. |
| 1 | Requirements & bidirectional traceability | **PARTIAL** (tooling now exists) | 620 `REQ-*` ids defined across 89 files in `doc/02_requirements/**`; `@req` links in specs. NEW checker `scripts/check/cert/check-req-traceability.shs` (self-test PASS, 0.8s). Live: **175/620 traced-down (28%)**, **445 orphan-down**, **244 orphan-up**. | Orphan burndown; some orphan-up are id-hygiene noise (prefix-only `REQ-CONC`, `REQ-0`); design layer not yet linked. | FAIL @ A/D-auto until orphans resolved; WARN below. |
| 2 | Coding std + static analysis | **PASS** (infra present) | `bin/simple build {lint,fmt,check}`; `scripts/audit/*` guards (`direct-env-runtime-guard.shs`, `numbered-artifact-guard.shs`, `naming_consistency_audit.spl`, `api_consistency_audit.spl`, `noalloc_reachable_imports.spl`); `scripts/check/*guard*.shs`. | Not re-run in this pass (no big build); JPL Power-of-10 assertion-density + no-UB-in-codegen not separately gated. | statement-tier PASS. |
| 3 | Structural coverage (incl. MC/DC) | **PARTIAL** | `src/app/coverage` (statement coverage via test runner). `std.mcdc` **analysis** library in two tiers: `src/lib/nogc_sync_mut/mcdc.spl`, `src/lib/gc_async_mut/mcdc.spl` (+ `mcdc_spec.spl`) — `register_decision`/`record_evaluation`/independence pairs. **No MC/DC in `src/compiler`** — not wired into codegen. | Codegen-level condition instrumentation + whole-program report (C1). | Statement measurable; MC/DC NOT a measured criterion. |
| 4 | Test rigor (normal/robustness/stress/opt) | **FAIL** (for A) | Robustness breadth strong: **2209** `*_spec.spl` carry negative/robustness tokens (reject/invalid/out-of-range/fail-loud). But: opt-soundness sweep is scaffold-only and the reference gate `scratchpad/redeploy_gate.sh` is **not in-tree** (ephemeral); no sanitizer matrix (C4); no differential fuzzer (C3); seed codegen still miscompiles enum handles (wall). | A miscompilation is auto-FAIL per skill rules; full differential sweep missing. Deployed pure-Simple `bin/simple` passes known repros, so product robustness is strong. | Robustness supports D/auto-A; opt-soundness blocks A. |
| 5 | Determinism / reproducibility | **PASS** | `238d86c1dc4` deterministic entry-shim (per-PID dir + fixed `simple_entry.c` basename); build-twice sha256 mechanism-proven. | Reproducibility gate not yet CI-wired across all targets. | PASS. |
| 6 | Formal verification (DO-333) | **PARTIAL** | 27 Lake projects under `src/verification/`; `scripts/check/check-lean-proofs.shs` (zero `sorry`/`admit`/axiom gate via `TRUST_RE`); `scripts/rtl/check-rvfi-formal-readiness.shs`. | Codegen semantic-preservation (CompCert-style) or per-compile translation validation unproven. | Seed of a DO-333 case, not full. |
| 7 | Tool qualification (the compiler) | **BLOCKED** | 3-stage bootstrap fixpoint (stage2==stage3) = partial self-consistency only. No ACATS/GCC-torture qualified validation suite (C7). Seed-built stage4 miscompiles the ANY-erased `Dict<text,Value>`/enum-payload channel (seed cranelift only; see `redeploy_selfhost_plan.md`). | Qualified validation suite runnable NOW on the clean `bin/simple`; the seed wall blocks only seed-built stage4, not the pure-Simple product. | FAIL/BLOCKED on corpus, not on the backend. |

## Overall nearest-achievable grade (today)

**`aero-d` / `auto-a`** (statement coverage + robustness) — and even that is **gated** on:
1. resolving/annotating the **445 orphan-down + 244 orphan-up** traceability findings the new
   C5 checker surfaces (Phase 1), and
2. authoring the **5 lightweight Phase-0 plan docs**.

Everything above C (branch/MC/DC coverage + tool qualification) is **BLOCKED** behind the
stage4 wall.

### Ordered blockers

1. **stage4 tag/box wall** (seed cranelift `BoxInt`, `codegen/instr/mod.rs:1305`) — root; blocks
   Phase-7 tool-qualification and trustworthy Phase-3/4 numbers.
2. **No codegen structural-coverage instrumentation** (Phase 3) — `std.mcdc` is manual-only;
   C1 is blocked by #1.
3. **Traceability orphan burndown** (Phase 1) — checker now exists; 445 down + 244 up to
   resolve or annotate (incl. id-hygiene normalization).
4. **Missing Phase-0 plan docs** (PSAC/SDP/SVP/SCMP/SQAP equivalents).
5. **Full opt-soundness sweep + sanitizer matrix + differential fuzzer** (Phase 4: C2/C3/C4) —
   absent or scaffold-only.
6. **Codegen semantic-preservation proof** (Phase 6).

## Root ordering constraint (CORRECTED 2026-07-05)

The stage4 wall is **seed-cranelift-only** (mis-lowers the ANY-erased `Dict<text,Value>`/
enum-payload channel — see `redeploy_selfhost_plan.md`; the "BoxInt" and "by-name
struct-registry collision" hypotheses were both falsified this session). The pure-Simple
codegen used by deployed `bin/simple` is **clean** and passes all soundness repros.

**Therefore the wall does NOT block cert-evidence gathering.** MC/DC instrumentation
(C1), optimization-soundness differential (C2), and the tool-qualification validation
suite (C7) are all **runnable NOW on the clean `bin/simple`** — the differential's
interpret-vs-compiled oracle validates the actual pure-Simple product. The wall blocks
only (a) redeploying the ~130 frozen source fixes via a **seed-built** stage4 (deferred —
use the pure-Simple self-host path in `redeploy_selfhost_plan.md`) and (b) tool
qualification of the *seed* specifically. Do the flight-level evidence work on
`bin/simple` first; treat redeploy as an independent deferred track.

## Deferred task queue (time-consuming — run detached / cron)

| # | Task | Owner | Trigger | Status |
|---|---|---|---|---|
| C1 | MC/DC instrumentation + report | codegen | after wall fix | **blocked (wall)** — `std.mcdc` analysis lib exists but not codegen-wired |
| C2 | Full optimization-soundness sweep (interp×cranelift×llvm × O0/O2) | verify | nightly cron | scaffold only; reference gate `scratchpad/redeploy_gate.sh` not in-tree |
| C3 | csmith-style differential fuzzer | verify | nightly cron (time-boxed) | queued |
| C4 | Sanitizer matrix (ASan/UBSan/TSan/MSan) of seed + C runtime | infra | nightly cron | queued |
| C5 | Bidirectional traceability generator + orphan report | docs | every test run | **scaffold LANDED** — `scripts/check/cert/check-req-traceability.shs`; orphan burndown open |
| C6 | WCET / timing analysis | infra | on-demand (real-time claims) | not-scheduled |
| C7 | Tool-qualification validation suite (ACATS/torture analog) | verify | after wall fix | queued |

## Landed (cert-relevant this initiative)

- **Traceability scaffold (Phase 1 / C5):** `scripts/check/cert/check-req-traceability.shs` —
  pure-POSIX `.shs`, bidirectional orphan detector (`--strict`, `--self-test`, `--help`),
  writes `build/cert/req_traceability_report.md` (gitignored). Baseline: 620 defined,
  175 traced-down, 445 orphan-down, 244 orphan-up.
- **Determinism / reproducibility (Phase 5):** bootstrap entry-shim filename made deterministic
  (`238d86c`) — build-twice sha256 matches. Mechanism-proven.
- **Formal (Phase 6, partial):** 27 zero-sorry Lean projects; `check-lean-proofs.shs` gate;
  RVFI readiness script.
- **Struct-registry hardening:** `SymbolId`->`SymbolName`, `Symbol`->`DepSymbol` collisions removed
  (`10a1f70`, `0b2b26fa`) — removes a value-corruption vector (traceability/robustness relevant).

## Next actions

1. Fix the stage4 wall (`BoxInt` heap-handle tag-awareness) — unblocks C1, C7, and Phase-4/7.
2. **C5 orphan burndown** — triage the 445 orphan-down + 244 orphan-up findings; normalize
   id-hygiene (prefix-only `REQ-CONC`, `REQ-0`), add missing `@req` links or requirements.
3. Author the 5 Phase-0 plan docs (PSAC/SDP/SVP/SCMP/SQAP equivalents) under `doc/03_plan/cert/`.
4. Wire C2/C3/C4 as nightly cron under `scripts/check/cert/`.
