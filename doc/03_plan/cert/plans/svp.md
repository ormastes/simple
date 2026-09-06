# Software Verification Plan (SVP)

Companion to `psac.md`/`sdp.md` (DO-178C §11.3/§6). Defines verification methods, maps
each to an existing repo artifact, and states independence + verification-of-verification
posture. Target grade: aero-d/auto-a nearest-achievable; gaps to aero-a (MC/DC + tool
qualification) called out explicitly per `cert_roadmap.md`.

## Verification methods → artifacts

| Method (DO-178C §6.2) | Artifact | Status |
|---|---|---|
| **Reviews** (requirements/design/code) | `code-review` skill (invoked pre-merge on diffs); `.claude/rules/*` as review checklist | present, not independence-gated (see below) |
| **Analysis** — coding standard conformance | `bin/simple build lint`; `scripts/audit/{naming_consistency_audit.spl,api_consistency_audit.spl,noalloc_reachable_imports.spl,repo_hygiene_audit.spl}` | present |
| **Analysis** — formatting conformance | `bin/simple build fmt --check` | present |
| **Analysis** — structural/manifest guards | `scripts/check-workspace-root-guard.shs` (FILE.md), `scripts/audit/numbered-artifact-guard.shs`, `scripts/check/check-api-arch-guard.shs` | present |
| **Analysis** — requirements traceability | `scripts/check/cert/check-req-traceability.shs` (bidirectional orphan detector, self-test PASS, writes `build/cert/req_traceability_report.md`) | present; 445 orphan-down / 244 orphan-up open |
| **Test** — requirements-based, functional + robustness | `test/**/*_spec.spl` (22,875 spec files), run via `bin/simple test`; 2,209 specs carry explicit negative/robustness tokens (reject/invalid/out-of-range/fail-loud) | present, strong robustness breadth |
| **Structural coverage** — statement | `src/app/coverage` (test-runner-driven statement coverage) | present |
| **Structural coverage** — MC/DC | `std.mcdc` analysis library (`src/lib/{nogc_sync_mut,nogc_async_mut,gc_sync_mut,gc_async_mut}/mcdc.spl` + `mcdc_spec.spl` per tier): `register_decision`/`record_evaluation`/independence-pair check API | library exists, **not wired into codegen** — manual-only, not a measured criterion yet (C1) |
| **Optimization-soundness** (interp vs compiled, opt levels) | planned `scripts/check/cert/soundness-diff.shs` (generalizes the ephemeral `scratchpad/redeploy_gate.sh` pattern into an in-tree, corpus-driven differential) | scaffold-only today (C2) |
| **Formal verification** | 27 zero-`sorry`/`admit`/axiom Lake projects under `src/verification/` (actor_channel, kernel_scheduler, gc_boundary, db_storage, fat32, ui_compositor, memory_model_drf, tls_isolation, ffi_contract, ... — model-checker-rule soundness, concurrency-runtime, storage invariants), gated by `scripts/check/check-lean-proofs.shs` (auto-discovers Lake projects, `TRUST_RE` bans `sorry`/`admit`/`axiom`/`opaque`/etc. outside comments) | present for the modeled properties; **no codegen semantic-preservation proof** — see `formal_codegen_semantics_plan.md` |
| **Tool qualification** (of `bin/simple` as a development tool) | 3-stage bootstrap fixpoint (stage2==stage3 byte match) | partial — self-consistency only, not a qualified validation suite (C7) |

## Independence

- DAL D (current target) does not require independence between developer and verifier
  per DO-178C Table A-3/A-7. No independence gate is enforced today even where it would
  help (e.g., code review is commonly self-initiated by the change author's session).
- For any future DAL C/B/A claim: reviews and structural-coverage analysis require
  independence (a reviewer/analyst distinct from the author). This is **not yet
  implemented** — flagged as a Phase-2/3 gap, not just a Phase-6/7 one.

## Verification of verification

- The traceability checker, lint/fmt gates, and `check-lean-proofs.shs` each have a
  `--self-test` mode that exercises known-good/known-bad inputs and asserts the expected
  PASS/FAIL classification (e.g. `check-lean-proofs.shs --self-test` plants 5 known trust
  bypasses in a synthetic Lean file and asserts exactly 5 are caught) — this is the
  verification-of-verification evidence for the analysis tools themselves.
- The `std.mcdc` library has its own `mcdc_spec.spl` per tier, verifying the independence-
  pair logic against hand-built decision tables — but this only verifies the *library*,
  not a codegen instrumentation pass, since none exists yet (C1).
- No verification-of-verification exists yet for the (unbuilt) soundness-diff and
  sanitizer-matrix scripts, since they are not implemented (C2/C4).

## Gap to MC/DC-at-DAL-A

1. **C1 — MC/DC codegen instrumentation** is the primary blocker: `src/compiler/70.backend`
   needs a `SIMPLE_COVERAGE=mcdc` instrumentation pass emitting per-condition probes for
   every `if`/`while`/`match`-guard/`and`/`or`, plus a post-processing independence-pair
   verifier and per-module report. Until this lands, statement coverage is the only
   measured criterion — acceptable for aero-d/auto-b, explicitly **not** sufficient for
   aero-a/auto-d/space-a and must never be mislabeled as MC/DC (per `cert_roadmap.md`
   Phase 3 and the deferred-tasks plan C1 acceptance criteria).
2. **C2 — optimization-soundness differential** must run clean (0 divergences,
   interpret vs cranelift-O0 vs cranelift-O2) before MC/DC numbers on compiled code are
   trustworthy evidence rather than numbers from a possibly-miscompiling backend. Note:
   the stage4 wall is seed-only (corrected 2026-07-05); the clean `bin/simple` codegen is
   the one that needs this differential, and it is runnable now.
3. **C7 — tool qualification** (ACATS/GCC-torture analog corpus) is required before
   `bin/simple` itself can be trusted as a DAL-A verification tool without additional
   independent manual verification of its output.
4. **Independence** enforcement (reviewer ≠ author, analyst ≠ author) is undesigned for
   any tier above D.
5. **Formal codegen semantic-preservation** (DO-333) is a separate, currently-zero-coverage
   gap — see `formal_codegen_semantics_plan.md`.
