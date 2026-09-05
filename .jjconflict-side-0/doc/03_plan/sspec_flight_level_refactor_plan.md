# Plan: Flight-Level SSpec Refactor & 100% MC/DC Path

Status: plan · 2026-07-05 · Domain: infra / cert · Owner: cert + spipe lanes
Builds on: `doc/03_plan/sspec_modernization_plan.md` (Modern SSpec Phases 1–5)
Cert deps: `doc/03_plan/cert/cert_roadmap.md`, `doc/03_plan/cert/deferred_tasks_plan.md` (task **C1**)
Policy: `.claude/skills/cert_grade.md` (MC/DC required at aero-A / auto-D / space-A; never claim MC/DC from statement coverage)
Guides: `doc/07_guide/app/spipe/mission_critical_robust_sw.md`, `doc/07_guide/infra/sspec_antipatterns.md`
Scope: PLAN ONLY. No implementation, no spec edits in this document.
Discovery baseline: verified 2026-07-05 (counts below are as-of; do not re-scan mid-wave).

## Goal

Bring the whole owned repo — Simple compiler, SimpleOS baremetal, NVMe FW, and
the remaining SW — onto Modern SSpec and onto a **measured** MC/DC path, staged
so the flight-critical buckets (FW, OS, compiler trusted core) reach **100%
MC/DC first** while the long tail lands statement+branch with explicit,
per-`cert_grade` rationale. Success = MC/DC % is *measured* per bucket by new
self-hosted instrumentation (C1c reporting) and never inferred from statement
coverage, and every touched spec passes the anti-patterns lint.

## Why a new plan (not just C1)

C1 delivers the *instrument*; this plan delivers the *coverage campaign* that
consumes it, plus the structural cleanup that makes effort estimates real. The
two tracks are deliberately decoupled: MC/DC enablement (§2) can proceed while
porting waves (§3) run, because porting produces the requirements-based tests
that the instrument then measures.

## Discovery baseline (as-of 2026-07-05, do not re-scan)

MC/DC infra today:
- Rust seed only: `MirInst::DecisionProbe`/`ConditionProbe`
  (`inst_enum.rs:665,678`) → Cranelift `rt_decision_probe`/`rt_condition_probe`;
  runtime records **percentages only, no independence-pair computation**
  (`runtime/src/coverage.rs:190-238`). LLVM backend no-ops probes
  (`functions.rs:1621`); VHDL backend **rejects** them (`codegen.rs:319`);
  interpreter stub.
- Self-hosted `src/compiler`: **no instrumentation at all** (roadmap:29). This is
  the default toolchain per bootstrap rules → C1 = wire probes into self-hosted
  codegen.
- `std.mcdc` analysis lib exists (`src/lib/nogc_sync_mut/mcdc.spl`, 337 lines,
  independence-pair structs) but its spec is 78/85 lines commented out.
- Runner measures statement/line only; branch/condition disabled at
  `test_runner_main.spl:205-207`.

Spec inventory (`test/`): 22,877 `*_spec.spl`, ~3.57M lines. Buckets: compiler
2,346 files / 393k lines (44% docstrings, 5 files use `step()`); simpleos
baremetal 710 / 94.6k (32%, 12 `step()`); nvme_fw 8 / 952 (100% docstrings,
8/8 `step()` — the model bucket); rest 19,813 / 3.08M (53%, 308 `step()`).
`@manual_section` ≈ 0 repo-wide. ~3,024 files flagged amateur (trivial it-names).
**Structural debt:** 5,796 files (25%) are auto-generated
`.spipe_matchers_*` / `.spipe_wrapped_entry_*` duplicates; legacy `test/unit/`
(5,041 files) mirrors `test/01_unit/` (10,413).

Source decision density (MC/DC sizing, vendored excluded): compiler 40,544
decisions / 12,562 fn / 350k lines; simpleos_nvme_fw 2,011 / 283 / 12.5k;
nogc_async_mut_noalloc 1,844 / 1,074 / 22.4k; `src/lib` 118,038 / 43,726 / 88.7k;
`src/app` 49,940 / 14,798 / 321k. **Total ~212k decision sites / 72.4k fn.**

---

## 1. Wave 0 — Structural cleanup (before any porting estimate)

Estimates are meaningless while 25% of `test/` is auto-generated duplicate and a
5,041-file legacy tree shadows the real one. Do this first so all later counts
are a true baseline.

- **Dedup auto-generated artifacts.** Decide policy for
  `.spipe_matchers_*` / `.spipe_wrapped_entry_*` (5,796 files): *regenerate-on-
  demand* (gitignore + a `spipe-docgen`/runner regen step) vs *commit as
  build output*. Prefer regenerate-on-demand unless a consumer needs them in
  VCS. Record the decision as an ADR under `doc/04_architecture/*/adr/`.
- **Merge legacy `test/unit/` → `test/01_unit/`.** Reconcile the 5,041 shadow
  files against the 10,413 canonical ones; delete duplicates, migrate any
  unique cases, remove the legacy tree.
- **Sequencing risk:** parallel agent sessions force-push `test/`. Do Wave 0 as
  one short, well-announced lane (root-first conflict loop per `vcs.md`), commit
  in small lots, verify with `git log --stat` after each.
- **Acceptance:** spec count drops to a true baseline (report new totals per
  bucket in `doc/09_report/`), `bin/simple test` / `build check` green, no
  dangling references to removed paths.

---

## 2. MC/DC enablement track (independent of porting — implements cert C1)

Runs in parallel with §3 (disjoint files: codegen/runtime/runner vs `test/`).
Reference deferred task **C1** for the codegen instrumentation detail.

- **C1a — Instrument self-hosted codegen.** Add the Decision/ConditionProbe
  emission pass to `src/compiler/70.backend` under `SIMPLE_COVERAGE=mcdc`
  (each boolean sub-expr of every `if`/`while`/`match`-guard/`and`/`or` gets a
  unique id). Mirror the seed's probe semantics so seed and self-hosted agree.
- **C1b — Independence-pair computation.** Extend `std.mcdc`
  (`src/lib/nogc_sync_mut/mcdc.spl`) and the runtime record format
  (`runtime/src/coverage.rs`) to record `(condition-vector, outcome)` tuples and
  compute, per decision, whether each condition has an independence pair
  (toggled while others fixed → outcome flips). Replace percentage-only output.
- **C1c — Runner integration.** Re-enable branch/condition at
  `test_runner_main.spl:205-207`; emit an **MC/DC report per file + per-DAL
  gate** in `bin/simple test` / `build check`. Report format must state coverage
  kind explicitly (statement / branch / MC/DC) so nothing is mislabeled.
- **C1d — Prove the lib.** Un-comment the 78/85 commented lines of `mcdc_spec.spl`
  and make them pass against C1b; this is the self-test of the measurement.
- **VHDL caveat:** the VHDL backend rejects probes (`codegen.rs:319`) — MC/DC
  builds must route through a probe-strip pass or a non-VHDL target for
  instrumented runs (see §7 risk).
- **Acceptance:** MC/DC % report per module on a sound backend; every uncovered
  condition is tested, justified (deactivated/defensive), or removed.

---

## 3. Per-target refactor waves (priority = criticality × tractability)

Each wave = Modern-SSpec port (§4 mechanics) + a coverage target measured by C1c.
100% MC/DC is claimed only where stated, and only from C1c output.

### Wave 1 — NVMe FW pilot (smallest, already modern)
- **Bucket:** nvme_fw, 8 specs (100% docstrings, 8/8 `step()`), `fw_rv32`
  2,011 decisions / 283 fn.
- **Goal:** **100% MC/DC** on `fw_rv32`; all 8 specs Modern SSpec with
  `bit_table` captures + per-run `req_trace`. Proves the whole chain
  (instrument → independence pairs → report → traceability) end-to-end on the
  cheapest target.
- **Size:** M.

### Wave 2 — SimpleOS baremetal
- **Bucket:** `noalloc` tier + `src/os`; 710 specs, ~1,844 decisions (noalloc) +
  os core.
- **Goal:** **100% MC/DC** on the baremetal safety core; `bit_table` captures for
  register/protocol state.
- **Size:** L.

### Wave 3 — Compiler trusted core
- **Bucket:** compiler, 40,544 decisions total. Define the **trusted-core
  subset** explicitly: frontend parser + type system + the codegen layers.
- **Goal:** **100% MC/DC for the trusted-core subset** at its DAL target;
  **statement+branch elsewhere** in the compiler with a written rationale per
  `cert_grade` policy (never claim MC/DC on the non-core remainder).
- **Size:** XL.

### Wave 4 — Stdlib safety tiers
- **Bucket:** `src/lib`, 118,038 decisions. Tiered targets: **100% MC/DC** for
  `common/` + `nogc_sync_mut` safety-critical modules; **branch** for the rest.
- **Goal:** nogc tiers first (they underpin FW/OS), then GC tiers.
- **Size:** XL.

### Wave 5 — Apps + long tail
- **Bucket:** `src/app` 49,940 decisions + the ~3,024 amateur specs.
- **Goal:** Modern-SSpec port in **agent batches** (haiku/sonnet, 50-file lots,
  lint gate per lot); coverage target **statement+branch** with MC/DC only where
  an app makes a safety claim.
- **Size:** XL (long tail; staged, not blocking earlier waves' DoD).

---

## 4. Modern-SSpec porting mechanics (per wave)

Applied uniformly; reuse the modernization plan's Phase-5 machinery.
- **Checklist:** `doc/07_guide/infra/sspec_antipatterns.md` — kill trivial
  it-names, add user-voice `"""..."""` docstrings, imperative `step("...")` /
  `@step` helpers, `@manual_section` groupings, `# @req REQ-*` traceability.
- **Capture kinds per domain:** `bit_table` for FW/OS; `tui_grid` / `gui_image`
  for apps; `statistics` for perf-bearing specs. Reviewed goldens per capture.
- **Lint gate (regression guard):** turn on the modernization Phase-5 lint rule
  **per directory as each wave completes**, so a completed bucket cannot regress
  into amateur specs. New/edited files in a completed bucket must pass before
  merge.

---

## 5. Effort model (rule of thumb: ~1 unit test per decision for MC/DC pairs, batched)

| Wave | Bucket | Spec files touched | Decisions to cover | Est. new unit tests | Agent-lot sizing | Size |
|------|--------|--------------------|--------------------|---------------------|------------------|------|
| 0 | dedup + legacy merge | ~10,837 removed/merged | — | — | 1 focused lane | M |
| 1 | nvme_fw | 8 | 2,011 (100% MC/DC) | ~2.0k | 1 lot | M |
| 2 | simpleos baremetal | 710 | ~1.8k+ core (100% MC/DC) | ~1.8k+ | 50-file lots | L |
| 3 | compiler trusted core | subset of 2,346 | trusted subset of 40,544 (100%); rest branch | ~15–25k (subset) | 50-file lots | XL |
| 4 | stdlib safety tiers | subset of ~lib specs | nogc/common subset of 118,038 (100%); rest branch | ~40–60k (tiered) | 50-file lots | XL |
| 5 | apps + long tail | 3,024 amateur + app specs | 49,940 (stmt+branch) | port-driven | haiku/sonnet 50-file lots | XL |

Numbers are planning envelopes; C1c measurement replaces estimates once each
bucket is instrumented. "~1 test per decision" is a sizing heuristic — batched
tests exercise multiple independence pairs per case, so realized counts run
lower.

---

## 6. Gates & traceability

- **REQ IDs:** allocate `REQ-SSPEC-FLIGHT-001..` — one range per wave (W0…W5),
  registered in `doc/02_requirements/**` and cited via `# @req` in each ported
  spec.
- **Per-wave DoD:** MC/DC % **by bucket, measured by C1c reporting** (§2), meets
  the wave's stated target; never claimed from statement coverage. Anti-patterns
  lint green for the wave's directory. New specs Modern-SSpec with required
  capture kind + reviewed golden.
- **Traceability tie-in:** feed `doc/08_tracking/trace/req_trace.md` (from
  modernization FR-6 / cert C5) so REQ↔spec↔code↔MC/DC-result is auto-updated
  per run; orphan-down (REQ with no test) and orphan-up (spec citing unknown
  REQ) must be empty at each wave's DoD.
- **Cert evidence mapping:** Wave 1/2 → PSAC/SVP structural-coverage sections for
  FW/OS DALs; Wave 3 → compiler tool-qualification (C7) coverage evidence;
  Waves 4/5 → supporting-component coverage. Each wave's DoD records which
  PSAC/SVP section its report populates, appended to `cert_roadmap.md`.

---

## 7. Risks

- **Probe overhead on a ~795k-line build.** Instrumented MC/DC runs may be slow /
  large. Mitigate: `SIMPLE_COVERAGE=mcdc` opt-in, per-bucket instrumented runs,
  not whole-repo-at-once; if a real perf regression appears, fix or file it in
  the same change (per repo rules).
- **Golden churn.** Adding capture goldens across thousands of specs invites
  noisy diffs; land goldens per-lot with review, never bulk-regenerate blind.
- **Parallel-session conflicts on `test/` during Wave 0 dedup.** High blast
  radius; run as one announced lane, root-first conflict loop, small commits,
  `git log --stat` verify after each.
- **Seed-vs-self-hosted divergence.** Probe semantics must match between the
  Rust seed (existing) and self-hosted codegen (C1a); a mismatch measures the
  wrong backend. Cross-check on the nvme_fw pilot before scaling.
- **VHDL backend rejects probes** (`codegen.rs:319`). Instrumented builds must
  route through a probe-strip pass or a non-VHDL target; do not gate VHDL specs
  on MC/DC directly.
- **Schedule realism for ~212k decisions.** 100% MC/DC repo-wide is **staged
  over waves, not achieved at once**. Only nvme_fw (W1), baremetal core (W2),
  and the compiler trusted-core subset (W3) reach 100% first; stdlib is tiered
  (W4) and apps/long-tail are statement+branch (W5). State this plainly in every
  status report so no bucket is over-claimed.
