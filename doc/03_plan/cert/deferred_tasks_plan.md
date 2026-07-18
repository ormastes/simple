# Cert Deferred-Tasks — Detailed Implementation Plans (for later)

These are the **long / mechanical** certification tasks, described in enough detail to
execute later without re-discovery. They are deliberately NOT run interactively — run
detached / cron. Root dependency for C1/C2/C3/C7: the **stage4 wall fix** (seed `BoxInt`
tag-awareness) must land first, else coverage/soundness/fuzz numbers measure a
miscompiling backend. C5 is the only one that is cheap AND not wall-blocked.

Tracking table + status lives in `cert_roadmap.md`. This doc is the HOW.

---

## C1 — MC/DC structural coverage instrumentation  *(hard-ish, wall-blocked)*
- **Goal:** measure Modified Condition/Decision Coverage on requirements-based tests → the criterion for aero-a / auto-d / space-a.
- **Approach:** in the pure-Simple codegen (`src/compiler/70.backend`), add an instrumentation pass that, under a `SIMPLE_COVERAGE=mcdc` flag, emits per-decision + per-condition probes (each boolean sub-expression of every `if`/`while`/`match`-guard/`and`/`or` gets a unique id; record the (condition-vector, outcome) tuples at runtime to a side file). Post-process: for each decision, verify each condition has an independence pair (toggled while others fixed, outcome flips). Report uncovered conditions.
- **Effort:** large. **Deps:** wall fix (measuring on a sound backend). **Acceptance:** MC/DC % report per module; every uncovered condition either tested, justified (deactivated/defensive), or removed.
- **Interim:** statement coverage via the existing runner is acceptable ONLY for aero-c/auto-b and MUST be labeled as such — never reported as MC/DC.

## C2 — Full optimization-soundness differential sweep  *(mechanical, cron)*
- **Goal:** prove the program behaves identically across execution modes / opt levels (Phase-4.5).
- **Approach:** generalize `scratchpad/redeploy_gate.sh` into `scripts/check/cert/soundness-sweep.shs`: for every `*_spec.spl` (or a curated corpus), run under {interpret, cranelift-O0, cranelift-O2, (llvm)} and diff outputs; any divergence = codegen defect, emit a report. Time-box; shard across the corpus.
- **Effort:** medium (mostly wiring). **Deps:** wall fix (else it just re-reports the wall). **Acceptance:** 0 divergences on the corpus; nightly cron green.

## C3 — Differential fuzzer (csmith-style)  *(hard, cron, time-boxed)*
- **Goal:** find miscompilations no hand test covers.
- **Approach:** a generator (`src/app/test/fuzz/`) emitting random VALID Simple programs from a grammar-weighted model (arithmetic, structs, enums, matches, generics, closures) with a computable expected output; oracle = interpret (reference) vs compiled. Minimize any divergence to a small repro. Seedable via `args` (no `Math.random` in-process).
- **Effort:** large. **Deps:** wall fix. **Acceptance:** N generated programs/night with 0 unexplained divergences; any finding auto-minimized + filed.

## C4 — Sanitizer matrix (ASan/UBSan/TSan/MSan)  *(mechanical, cron)*
- **Goal:** catch memory/UB/race/uninit defects in the Rust seed + C runtime that static analysis misses.
- **Approach:** `scripts/check/cert/sanitizer-matrix.shs`: build the Rust seed + C runtime under each sanitizer (`RUSTFLAGS="-Zsanitizer=address"` etc. on nightly; `-fsanitize=undefined,address` for the C runtime), isolated `CARGO_TARGET_DIR` per sanitizer, run the runtime + compiler unit suite. Collect + triage findings.
- **Effort:** medium. **Deps:** none (independent of wall). **Acceptance:** clean under each sanitizer, or each finding triaged with a fix/waiver.

## C5 — Bidirectional traceability generator  *(cheap, NOT blocked — in progress)*
- **Goal:** REQ↔design↔code↔test matrix + orphan detection (Phase-1). Highest cert value per effort.
- **Approach:** `.spl`/`.shs` tool scanning `doc/02_requirements/**` for REQ-NNN, and `*_spec.spl` + source for REQ references; report orphan-down (REQ with no test) and orphan-up (test/code citing unknown REQ). Wire into a check script.
- **Effort:** small. **Deps:** none. **Status:** being built by the cert gap-analysis lane. **Acceptance:** runs on the repo, lists orphans both directions.

## C6 — WCET / timing analysis  *(on-demand)*
- **Goal:** worst-case execution time bounds for any real-time claim (Phase-4.4).
- **Approach:** only when a component claims hard-real-time. Static WCET (bounded loops, no unbounded recursion — already a JPL-P10 lint target) + measured high-water under stress. Likely out of scope until an RT component exists.
- **Effort:** large, narrow. **Deps:** an actual RT requirement. **Acceptance:** documented WCET bound + evidence per RT component.

## C7 — Tool-qualification validation suite  *(hard, after wall)*
- **Goal:** DO-330 TQL / ISO 26262 tool-qualification evidence for the compiler itself (Phase-7).
- **Approach:** assemble a qualified validation test suite (ACATS/GCC-torture analog): a large corpus of programs with known-correct outputs exercising every language construct + codegen path, run every release, with a tool operational requirements doc + known-problem list. The 3-stage bootstrap fixpoint (stage2==stage3) is self-consistency evidence, not correctness.
- **Effort:** large, ongoing. **Deps:** wall fix (a qualifiable tool must not miscompile). **Acceptance:** corpus green every release; TOR + problem-report process documented.

---

## Execution wiring (when un-deferred)
- Runners live under `scripts/check/cert/*.shs`; nightly via cron; results appended to `cert_roadmap.md` and gated into `/cert_grade --gap`.
- Never mark a Phase PASS from a scaffold when the full deferred task is what the objective requires. Record the delta explicitly (see cert_grade.md rules).
