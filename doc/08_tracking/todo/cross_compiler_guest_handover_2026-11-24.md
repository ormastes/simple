# Cross-compiler guest handover — 2026-11-24

Status: paused at the user's request to save TODOs and close the session.
Resume native work only on a new user instruction. P3 remains skipped.

## Original scope and acceptance

Synchronize the GitHub handover work, complete SimpleOS lint/test runners with
both native and Simple linkers, verify them in actual guests, and land fixes
through reviewed PRs. Preserve all **24 cases**; **0/24 actual guest cases are
verified** at this handover.

| CPU | Native lint | Native test | Simple lint | Simple test |
|---|---|---|---|---|
| x86_64 | TODO | TODO | TODO | TODO |
| i686 | TODO | TODO | TODO | TODO |
| ARM64 | TODO | TODO | TODO | TODO |
| ARM32 | TODO | TODO | TODO | TODO |
| RV64 | TODO | TODO | TODO | TODO |
| RV32 | TODO | TODO | TODO | TODO |

Retain each case's actual guest execution, exit/output assertions, target,
linker, source/compiler/runtime identities and artifacts. Source scans, host
controls, archive checks and ELF inspection do not establish guest execution.

## Landed work and its limits

- ARM32 native fixes: [PR #11140](https://github.com/ormastes/simple/pull/11140).
  Compiler-rt archive composition: [PR #11144](https://github.com/ormastes/simple/pull/11144);
  actual archive run `45265790554` passed at producer `2ac6a512…`.
  These establish native/archive evidence, not SDK or guest admission.
- Launch-environment source fix: [PR #11282](https://github.com/ormastes/simple/pull/11282)
  **merged**, commit `e25ebb9b211fea35b03e44afab08086231ac81d5`.
  Its five actual host controls remain pending.
- SDK download-controller repair: [PR #11300](https://github.com/ormastes/simple/pull/11300)
  merged at `8f66183f03d0384cdbd0197451b421a426752b2a`.
  No SDK execution or budget change accompanied that two-reference fix.
- Loader requirements: [PR #11298](https://github.com/ormastes/simple/pull/11298)
  merged at `6622b0b6c089638ce4b582ba6c68c7489abac9cb`.
  Authentic SPK compiler identity does not prove full-CLI command support.

## Resume TODOs and admission limits

1. Select a role-correct full CLI. Then execute the five guest-owner host
   controls, the enabled SDK observer control and eight SDK observer tests;
   preserve individual results and actual case counts. Complete required
   compiler/lib/MCP/LSP source checks and native smokes with a qualified runtime.
   The original SDK HIR-body failure remains unresolved.
2. Linux generation-two alternative: Astra reviewed controller SHA256
   `6270874fc1a7fee7aba4840e2f04c35109dc045382dab55272e2cefe7452d720`.
   Proposed campaign attempt **8** still requires explicit user alternative
   selection/admission. The actual campaign maximum remains **7**. No new
   claim, compiler execution or canonical stage-two admission occurred; the
   identity guard remains unchanged. This proposal does not authorize P3.
3. ARM wiring: actual canonical run `45361625031` failed on one unwired native
   float guard and two stale opt-outs. Its one-shot claim is consumed; the
   obsolete unassigned run `45273830620` was cancelled. The manual repair,
   native qualification and repaired full scan still need an explicit bounded
   approval and qualified capacity. Reuse of the unchanged prior 43 passing
   selftests is source-reviewed; full structural scan success is still needed.
   Mac capacity requires actual **arm64, macOS >=26.2 and RAM >=14 GB** before
   claim/execution, or select the reviewed Linux alternative. Capacity manifests
   remain unapproved; do not infer compatibility from a runner label.
4. RV32 has **one remaining bounded extension cycle**. Preserve existing
   source/native evidence and use that remaining cycle only within its recorded
   scope; actual Simple/MMU/guest qualification remains pending.
5. Finish all 24 guest cases and land remaining fixes after Astra review.
   Preserve other sessions' files. Do not reset consumed claims, restart capped
   campaigns, repeat green checks, add automatic retries, use the Rust seed for
   production checks, or publish release tags without the required approval.

## Preserved local resume evidence

- `C:/dev/simple-xc-handover/` — owned handover lane; preserve unrelated dirty files.
- `C:/dev/simple-xc-p2-priority-20261124/build/verify/linux-generation2-alternative/`
  — `final-status.sdn`, controller, workflow, ABI qualifier, watchdog and ledger;
  source-reviewed proposal, not runtime evidence.
- `C:/dev/simple-xc-guest-command-20261124/build/verify/guest-command-cycle2/`
  — offline SPK/tar roles and loader evidence, proposed capacity gate and
  `proposed-capacity-admission.sdn` with approval fields still false.
- `C:/dev/simple-arm32-canonical-wiring-hosted-20261124/build/verify/`
  — actual failed `arm32-canonical-wiring-45361625031/` receipt and
  `arm32-wiring-repair-proposal/`; the macOS-15 route is withdrawn.
- `C:/dev/simple-xc-handover/build/verify/readonly-surface-consumer-45291630645/`
  — successful prebody captures and final diagnosis; failing SDK worker context
  was not retained and body equivalence is unproved.

This TODO saves the full remaining scope. It grants no execution, budget reset
or native-cycle approval.
