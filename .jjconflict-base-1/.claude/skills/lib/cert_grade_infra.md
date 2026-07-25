# Cert-Grade Infra & Deferred-Task Queue

Companion to `.claude/skills/cert_grade.md`. Concrete infrastructure to build the certification evidence, and the **queue of time-consuming tasks that are deliberately deferred** (run via cron/background, never block an interactive turn). A grade is not "achieved" while any required task here is still queued — the queue IS the gap.

## Infrastructure to build (scaffolding → full)

| Capability | Now (scaffold) | Full (deferred) | Cert phase |
|---|---|---|---|
| **Structural coverage** | statement coverage via existing test runner | **MC/DC instrumentation** in codegen + report generator | 3 |
| **Differential soundness** | `scratchpad/redeploy_gate.sh` (14 checks, interpret-vs-compiled) | full `-O0/-O2` × interp/cranelift/llvm matrix over the spec corpus + **csmith-style fuzzer** | 4.5 |
| **Sanitizer matrix** | none | ASan/UBSan/TSan/MSan builds of Rust seed + C runtime, run over test suite | 4.6 |
| **Traceability** | manual REQ links in spec docstrings | auto-generated **bidirectional matrix** (REQ↔design↔code↔test), orphan detector | 1 |
| **Determinism** | build-twice sha256 (bootstrap det. fix landed) | reproducibility gate in CI over all targets | 5 |
| **Formal** | 27 zero-sorry Lean projects; RVFI readiness script | codegen semantic-preservation (CompCert-style) or per-compile translation validation | 6 |
| **WCET / timing** | none | worst-case execution time analysis for real-time claims | 4.4 |
| **Tool qualification** | 3-stage bootstrap fixpoint | qualified validation test suite (ACATS/GCC-torture analog) + tool operational reqs | 7 |

## Deferred-task queue (time-consuming — run detached)

These are long (minutes→hours) and MUST be postponed off the interactive path. Each has an owner and a trigger. Track status in `doc/03_plan/cert/cert_roadmap.md`.

1. **MC/DC instrumentation** — add condition-level coverage tracking to the pure-Simple codegen + a report. Owner: codegen. Trigger: after the stage4 wall (`BoxInt` tag-awareness) is fixed, since MC/DC on a miscompiling backend is meaningless. **Blocked-by: wall.**
2. **Optimization-soundness sweep (full)** — every `*_spec.spl` run under interp / cranelift / (llvm) and `-O0/-O2`, diffs collected. Owner: verify. Trigger: nightly cron. Partial today via redeploy_gate.
3. **Differential fuzzing** — csmith-style random valid-program generator + oracle (interp reference vs compiled). Owner: verify. Trigger: nightly cron, time-boxed.
4. **Sanitizer matrix** — build the Rust seed + C runtime under ASan/UBSan/TSan/MSan; run the runtime + compiler test suite. Owner: infra. Trigger: nightly cron. `CARGO_TARGET_DIR` isolated per sanitizer.
5. **Bidirectional traceability generator** — parse REQ-NNN across `doc/02_requirements/**`, link to design/code/test, emit orphan report. Owner: docs. Trigger: every test run (fast enough) or on-demand.
6. **WCET analysis** — only if/when real-time guarantees are claimed. Owner: infra. Trigger: on-demand.

## Cron wiring (postponed execution)

Long tasks are wired as detached/cron jobs, not interactive builds. Pattern:
- write the runner as a `.shs` under `scripts/check/cert/`,
- schedule nightly (cron) or launch `run_in_background`,
- append results + status to `doc/03_plan/cert/cert_roadmap.md` and gate them into `/cert_grade --gap`.

Never mark a cert objective PASS from a scaffold when the full deferred task is what the objective actually requires (e.g. statement coverage ≠ MC/DC). Record the delta explicitly.

## Ordering constraint

The **stage4 tag/box wall is the root blocker** for the compiler's own tool-qualification and for meaningful coverage/soundness numbers: a miscompiling backend fails Phase-4 (optimization-soundness) and Phase-7 (tool qualification) by construction. Fix the wall (`BoxInt` heap-handle tag-awareness in the seed cranelift codegen) first; then the deferred coverage/fuzz/sanitizer tasks produce trustworthy evidence.
