# Cert-Grade Skill — Safety-Critical Certification Readiness Codex

**Self-sufficient.** Any LLM (Claude, Codex, Gemini) can run this independently.

Brings code (esp. the Simple compiler + generated artifacts) toward **safety-critical / mission-critical certification grade** across aerospace, automotive, space, and military domains. This is the "how do we make it certifiable" codex — it defines the **grades**, the **objectives** per grade, and the **evidence** each objective requires.

> Certification is *evidence*, not vibes. Every claim in this skill must trace to a runnable check or an archived artifact. "It works" is not evidence; a coverage report, a traceability matrix, and a passing robustness suite are.

## Usage

```
/cert_grade                      # Assess current change against the target grade
/cert_grade --grade=aero-a       # Assess against a specific grade (see table)
/cert_grade --gap                # Full gap analysis: current state vs each grade
/cert_grade path/to/module.spl   # Assess one module + its tests
```

Argument: `$ARGUMENTS`

---

## The Grades

Simple defines four domain grades. Each maps to the governing standard's assurance level. Pick the **target grade** for the component under assessment.

| Simple grade | Domain | Standard | Assurance level | MC/DC required? |
|---|---|---|---|---|
| `aero-a` / `aero-b` / `aero-c` / `aero-d` | Airborne SW | **DO-178C** | DAL A / B / C / D | **A: yes**; B: decision cov; C: statement; D: none |
| `auto-d` / `auto-c` / `auto-b` / `auto-a` | Automotive | **ISO 26262** | ASIL D / C / B / A | **D: MC/DC**; C: branch; B/A: statement (Part 6 tbl) |
| `space-a` / `space-b` / `space-c` | Space flight SW | **ECSS-E/Q-ST-40C/80C** + **NASA NPR 7150.2** (Class A–E) | Category A / B / C · NASA Class A/B | Cat A ≈ MC/DC (per project) |
| `mil-hw` / `mil-sw` | Military | **DO-254** (electronic HW → RTL/VHDL output) + **MIL-STD-882E** + DEF STAN 00-055 | DAL A–E (HW) | per DAL A |

**Failure-condition severity drives the level** (DO-178C): Catastrophic→A, Hazardous→B, Major→C, Minor→D, No-effect→E. Automotive ASIL = Severity × Exposure × Controllability. Do not self-assign a level; derive it from a hazard/safety assessment (FHA/PSSA for aero, HARA for auto).

**Default posture for the Simple compiler itself:** treat it as a **development tool** under DO-330 / ISO 26262 tool qualification. A compiler that could insert an undetected error into safety code needs **TQL-1 (DO-330)** rigor *or* its output must be independently verified downstream (structural coverage on object code, or a qualified verified back-translation). The stage4 tag/box wall (miscompilation of enum handles) is exactly the class of defect tool qualification exists to catch — it is a **certification blocker**, not a cosmetic bug.

---

## Procedure

### Phase 0 — Planning & Scope (PSAC-equivalent)

1. Identify the **target grade** (arg or infer from the component's failure condition).
2. Confirm the five DO-178C plans exist (or their ISO 26262/ECSS equivalents), even as lightweight docs under `doc/03_plan/` / `doc/04_architecture/`:
   - **PSAC** (plan for software aspects of certification) · **SDP** (development) · **SVP** (verification) · **SCMP** (config mgmt) · **SQAP** (quality assurance).
3. Confirm coding/design **standards** are declared (Simple's equivalent of MISRA: `.claude/rules/*`, `doc/04_architecture/**/+rule/`). Missing plans → **WARN** (grade D/lower) or **FAIL** (grade A/D-auto).

### Phase 1 — Requirements & Bidirectional Traceability

The spine of every standard. Each requirement traces **down** to design→code→test and **up** from test→code→requirement, with **no orphans either way**.

1. Every `REQ-NNN` (`doc/02_requirements/**`) traces to: design (`doc/05_design/`), code (`.spl`), and ≥1 test (`*_spec.spl`).
2. **Derived requirements** (introduced by design/impl, not from a parent) are flagged and reviewed — they are where safety leaks hide.
3. **No dead code, no unintended function**: every line of source traces up to a requirement. Untraceable code = **FAIL** (A/D-auto) — it must be removed or a requirement added (never "convert TODO to NOTE"; implement or delete).

**Report:**
```
[PASS] REQ-014 → design §3.2 → parser.spl:fn parse_cfg() → cfg_spec.spl:it "strips inactive arch"
[FAIL] REQ-022 "shall reject NaN literal" — NO test (orphan requirement)
[FAIL] backend/objects.spl:fn alloc() — untraceable (no requirement; dead code or missing REQ)
[WARN] DERIVED: env.spl name-keying — introduced by impl to dodge stage4 SymbolId bug; needs review record
```

### Phase 2 — Coding Standard & Static Analysis

1. **Coding rules** enforced (Simple's MISRA analog): `bin/simple build lint` clean; no waived rules without a recorded deviation.
2. **Static analysis** clean at the target grade: run `bin/simple build check` + any `scripts/audit/*` guards (e.g. `direct-env-runtime-guard.shs`, `check-workspace-root-guard.shs`). For the Rust seed / C runtime, MISRA-C / clang-tidy / cppcheck / Frama-C equivalents apply.
3. **JPL Power-of-10 analogs** (space grade): bounded loops (no unbounded recursion in the hot compiler path), no dynamic allocation after init in safety-critical modules, assertion density ≥ 2/function on safety paths, check every return value, minimal scope.
4. **No undefined behavior in generated code** — the codegen must not emit UB (signed overflow, OOB, uninitialized reads). This is a compiler-specific hard requirement.

### Phase 3 — Structural Coverage (incl. MC/DC)

Coverage is measured on **requirements-based tests** (not tests written to chase coverage). Achieve the criterion for the target grade; **unreached code or unreached conditions must be explained** (dead code, deactivated code, or a missing test).

| Criterion | Meaning | Required at |
|---|---|---|
| Statement | every statement executed | aero-C, auto-B/A, space-C |
| Decision/Branch | every branch taken T and F | aero-B, auto-C |
| **MC/DC** | each **condition** independently shown to affect the decision outcome (unique-cause or masking) | **aero-A, auto-D, space-A** |

- MC/DC for a decision with N conditions needs **N+1 well-chosen test cases** minimum, each condition toggled while holding others fixed to prove independent effect (unique-cause or masking MC/DC; masking must be justified for optimizer short-circuited code).
- **Standard nuance (opus-verified):** DO-178C requires MC/DC **only at Level A**. ISO 26262-6:2018 (Table 9) *recommends* MC/DC across **all** ASILs, *highly recommended* only at **ASIL D** — so MC/DC evidence should not be omitted even at ASIL A/B. Statement coverage is HR at ASIL A/B; branch is HR from ASIL B.
- **Coverage is measured on the EXECUTABLE OBJECT CODE, not source estimates** (DO-178C §6.4.4.2). At **aero-A/B** also cover **data + control coupling** (Table A-7). Table A-7 **Obj.9 "additional code"** is compiler-critical: object code with no 1:1 source mapping — optimizer-restructured control flow (loop unroll, jump thread, dead-branch elim, tail-merge), **generic monomorphization**, enum/panic paths, runtime init — must be separately analyzed/exercised, else optimizations must be constrained. This is why an optimizing, monomorphizing compiler like Simple verifies at object-code level — and why the wall (miscompiled enum handles) is disqualifying.
- **Coverage gaps are analyzed, not deleted**: an uncovered branch is tested, justified as deactivated/defensive code (§6.4.4.3), or removed.
- Simple infra: the **`std.mcdc` analysis library already exists** (`src/lib/**/mcdc.spl`, two tiers) — C1 is "wire it into codegen at object-code level", not build-from-scratch. Until wired, record the gap — do NOT claim MC/DC from statement coverage.

### Phase 4 — Test Rigor (normal + robustness + stress + optimization)

Requirements-based testing must include **all** of these categories per grade:

1. **Normal-range**: nominal inputs, each equivalence class, each requirement's happy path.
2. **Robustness / NEGATIVE**: invalid inputs, out-of-range, malformed, boundary+1, resource exhaustion, error injection — the system must **fail safe / fail loud**, never silently produce wrong output. (Simple's silent-failure history — stubbed `ret 0`, fabricated symbols, `NIL`-as-error — is the anti-pattern this category exists to kill.)
3. **Boundary-value + equivalence-partitioning**: min, max, min−1, max+1, zero, empty, one, many, first/last.
4. **Stress / load / timing (WCET-aware)**: large inputs (993-module builds), deep nesting, long strings, concurrency stress, and — for real-time claims — worst-case execution time bounds.
5. **Optimization-soundness (differential)**: the program must behave **identically** across optimization levels and backends. Run each spec under `-O0/-O2`, interpret vs compiled, cranelift vs llvm; **any divergence is a codegen defect** (this is precisely how the stage4 wall was caught: `interpret=5` vs `compiled=<invalid operands>`). Differential/fuzz testing (csmith-style) against a reference is the gold standard for a compiler.
6. **Sanitizers / dynamic analysis** (Rust seed + C runtime): ASan (heap/stack OOB, UAF), UBSan (UB), TSan (data races), MSan (uninit reads), LeakSanitizer. Each catches a defect class static analysis misses. Run the runtime + seed test suite under each.

**Every fix ships with a regression test that fails on the pre-fix behavior** — no `skip()`, no weakened asserts (Simple crash-containment contract).

### Phase 5 — Determinism & Reproducibility

Certified builds must be **bit-reproducible** (same source + toolchain → identical binary). The bootstrap determinism fix (fixed `simple_entry.c` basename, no PID leak) is a Phase-5 requirement, not a nicety. Verify: build twice, `sha256sum` matches. Non-determinism = **FAIL** (blocks configuration control).

### Phase 6 — Formal Verification (where the grade demands / DO-333)

- Lean proofs (`src/verification/**`, `scripts/check/check-lean-proofs.shs`) with **zero `sorry`/`admit`/untrusted axioms** — the 27 zero-sorry projects are the seed of a DO-333 formal-methods case.
- RTL/DO-254: RVFI / riscv-formal / SymbiYosys evidence (`scripts/rtl/check-rvfi-formal-readiness.shs`).
- Semantic-preservation of codegen (CompCert-style) is the strongest compiler evidence; translation validation per-compile is a lighter alternative. Record which is claimed.

### Phase 7 — Tool Qualification (the compiler itself)

Assess the Simple compiler as a tool: does an error in it go undetected into safety code? It is a DO-330 **Criterion 1** development tool.

**The default industrial path is NOT to qualify the compiler** — it is to argue it *down* by verifying its output: full requirements-based testing + **structural coverage (incl. MC/DC) measured on the EXECUTABLE OBJECT CODE**, plus **diverse/double compilation** (compile with two independent toolchains/back-ends and diff — Simple already has interp vs cranelift vs llvm, which is exactly this). In ISO 26262 terms this is establishing **TD1** (high confidence tool errors are detected downstream) → **TCL1**, no tool qualification needed. This is the pragmatic route for Simple: fix the wall, then object-code coverage + differential compilation is the evidence — *not* a DO-330 qualification kit.

Formal qualification (TQL-1/2 · TCL3) is the alternative when downstream verification is infeasible: tool operational requirements, tool verification, a **qualified validation test suite** (ACATS/GCC-torture analog, C7), and known-problem reporting.

**Prior art for a self-hosted verified compiler:** **CakeML** — a formally-verified, *bootstrapped self-hosting* compiler proven in HOL4 (semantic preservation down to machine code). This is the single most relevant precedent for Simple and a far stronger endpoint than differential testing; Simple's 27 zero-sorry Lean projects are the seed of an analogous verified-compilation case. **CompCert** (verified C compiler in Coq, used in DO-178C settings) is the other reference. The self-hosted bootstrap's 3-stage fixpoint (stage2==stage3) is self-consistency evidence only — **not** correctness proof.

---

## Final Summary

```
== CERT-GRADE SUMMARY (target: aero-a / DO-178C DAL A) ==

Objective / Phase              | Status | Evidence
-------------------------------|--------|----------------------------------
0  Plans (PSAC/SDP/SVP/…)      | WARN   | lightweight; SVP missing
1  Requirements traceability   | FAIL   | 3 orphan REQ, 1 untraceable module
2  Coding std + static analysis| PASS   | lint+check clean
3  Structural coverage (MC/DC) | FAIL   | no MC/DC instrumentation yet (deferred)
4  Test rigor (neg/stress/opt) | FAIL   | optimization-soundness FAILs (stage4 wall)
5  Determinism / reproducible  | PASS   | sha256 match (bootstrap det. fix)
6  Formal verification         | PARTIAL| 27 zero-sorry Lean; codegen unproven
7  Tool qualification          | FAIL   | miscompilation defect open (wall)

GRADE STATUS: NOT YET aero-a. Blockers: MC/DC infra, optimization-soundness (wall), traceability.
Nearest achievable now: aero-d / auto-a (statement coverage + robustness).
```

## Rules (fail-closed)

- NEVER claim a coverage criterion you did not measure (statement ≠ MC/DC).
- NEVER count a happy-path-only suite as robustness-tested.
- A **miscompilation** or **optimization-dependent behavior** is an automatic **FAIL** at every grade — it is the defect certification exists to prevent.
- Untraceable code (no requirement) and orphan requirements (no test) are **FAIL** at A/D-auto, **WARN** below.
- Non-reproducible builds are **FAIL** (config control).
- Silent failure (stub `ret 0`, fabricated symbol, `NIL`-as-error, swallowed `Err`) is **FAIL** — it defeats robustness by construction.
- Deferred heavy tasks (MC/DC instrumentation, full sanitizer matrix, differential fuzzing, WCET) must be **recorded as explicit blockers with an owner**, never silently skipped. A grade is not "achieved" while a required objective is deferred.
- Read actual source, coverage reports, and traceability data — never trust names, comments, or a green summary alone.

## Applying to the Simple compiler

Run, in order (defer the slow ones per Phase-8 infra):
1. `bin/simple build check` (lint + fmt + tests) — Phase 2.
2. `scripts/check/check-lean-proofs.shs` — Phase 6.
3. `scripts/check/check-simpleos-mission-critical-release.shs` — SimpleOS release gate (must report `release_blockers=none`).
4. Differential optimization-soundness sweep (Phase 4.5) — the redeploy gate (`scratchpad/redeploy_gate.sh`) is a seed of this.
5. Determinism check (Phase 5) — build twice, compare sha256.
6. **Deferred / time-consuming (queue via cron or background, do not block a turn):** MC/DC instrumentation + report, full ASan/UBSan/TSan/MSan runtime matrix, csmith-style differential fuzzing, WCET analysis, full bidirectional traceability matrix generation. Track these in `doc/03_plan/cert/` with owners and gate them into `/cert_grade --gap`.

See companion: `.claude/skills/lib/cert_grade_infra.md` (infra + deferred-task queue) and `doc/03_plan/cert/` (grade roadmap).
