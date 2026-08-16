# Feature: qemu_simd_coverage_gate_lane

## Raw Request

Fresh scoped recovery session: "QEMU SIMD and coverage review routed to
non-overlapping checks; first confirm what is already pushed." Followed by:
"Add modern fail-closed step-based SSpec system coverage for this exact lane
under test/03_system ... If runtime is unavailable, record TEST_BLOCKED
honestly while keeping the future-executable spec fail-closed."

## Task Type

feature

## Refined Goal

Route the QEMU SIMD and SIMD-coverage review to non-overlapping checks, repair
whatever those checks actually prove to be broken, and leave behind a modern
step-based SSpec system test that re-proves the lane automatically once an
admitted pure-Simple CLI exists — fail-closed, with no skip path and no
placeholder pass.

## Acceptance Criteria

- AC-1: Confirm what is already pushed before doing anything, so no
  already-landed work is duplicated. **Met.** `origin/main` verified at
  `f6cadcc36aff`; the SIMD/coverage lane is largely landed there (arch-matrix
  evidence, 8k retained receipts, MIR coverage opcodes, per-layer coverage
  waves). Nothing was duplicated.
- AC-2: Route the review to non-overlapping checks. **Met.** SIMD half and
  coverage half separated; every check requiring a deployed `bin/simple`
  (arch-matrix, render2d-coverage) routed out and recorded as blocked rather
  than run against the Rust seed.
- AC-3: Each acceptance criterion verified once, from an isolated worktree at
  the proven commit, never from the shared dirty tree. **Met.**
- AC-4: Repair any defect the routed checks expose, smallest diff.
  **Met.** `check-simpleos-qemu-engine2d-simd-kernels.shs` was exiting 1 with
  zero output; one character (`\\{` → `\{`) restored it to a real PASS.
  Committed at `25dc443e44a`.
- AC-5: A modern step-based SSpec system test covers this exact lane with
  visible `step("...")` flows, built-in matchers, real positive/edge/error
  assertions, and REQ traceability. **Met.**
  `test/03_system/check/qemu_simd_coverage_gate_lane_spec.spl`, 4 scenarios,
  REQ-QEMU-SIMD-COV-LANE-001..006.
- AC-6: Mirrored Markdown manual authored under `doc/06_spec`, with no
  executable `.spl` placed there. **Met.**
  `doc/06_spec/03_system/check/qemu_simd_coverage_gate_lane_spec.md`.
- AC-7: Plan, guide, lane state, and lane feature-expert skill updated without
  touching a shared global skill owned by another pane. **Met.**
- AC-8: Runtime/docgen/sspec-maintain run only with an admitted pure-Simple
  CLI; otherwise TEST_BLOCKED recorded honestly. **Recorded as BLOCKED** — see
  Phase.

## Scope Exclusions

- QEMU guest hit/chunk receipts and QMP frame captures (other lane).
- `check-cpu-simd-engine2d-arch-matrix.shs` and `check-render2d-coverage.shs`
  — both require a deployed `bin/simple`.
- RenderDoc / Electron / Chrome comparison gates, the formal-coverage FPGA
  gate, and the x25519mlkem768 branch-coverage receipt: pre-existing reds
  belonging to other lanes, left untouched and not papered over.
- Phase 4 — explicitly out of scope, not touched.

## Cooperative Review

The shared `simple-main` worktree (3422 dirty entries) is treated as read-only
evidence. Its copy of the owned gate is BEHIND origin — it reverts origin's
`OBJDUMP` guard and reintroduces the already-fixed `dup ... \.4s` over-escape.
Nothing was taken from it; the fix is a forward delta on fetched `origin/main`.

Another pane owns the sosix QEMU matrix / parallel-QEMU feature-expert skills.
This lane created its own skill at
`doc/00_llm_process/feature_expert/qemu_simd_coverage_gate_lane/skill.md`
rather than editing theirs.

## Phase

verification-blocked: the executable spec, mirror, plan, guide section, lane
skill, and the underlying gate fix are complete. The lane is NOT verified and
NOT release-ready.

TEST_BLOCKED: no admitted pure-Simple CLI exists in this environment.
`bin/simple` resolves to the Rust bootstrap seed, which self-declares it must
not be used as the normal tool; `bootstrap/stage3/simple` answers `unknown
command 'test'`. Bootstrapping one is itself blocked:
`scripts/bootstrap/bootstrap-from-scratch.sh` exits 64 with
`bootstrap-policy-error: reason-receipt-required`, and the pure-Simple planner
that issues that receipt fails Stage 1 with `native-build worker timed out
after 180s before producing a binary`. Therefore `simple test`,
`simple spipe-docgen`, and `simple sspec-maintain` have NOT been run for this
lane, and no pass/fail is claimed for any scenario.

## Log

- review: Confirmed `origin/main` at `f6cadcc36aff`; created isolated worktree
  and branch rather than editing the shared dirty tree.
- review: Routed the lane to non-overlapping checks. Green on this host:
  `check-simpleos-qemu-engine2d-simd-kernels` (after fix),
  `check-engine2d-simd-c-kernels`, `check-x25519mlkem768-cpu-simd`,
  `check-gui-widget-rendering-fixture-coverage`,
  `check-nvme-baremetal-wrapper-coverage`, `check-engine2d-simd-8k-ops`.
- impl: Repaired the over-escaped `st1` ERE in the QEMU SIMD object gate. The
  gate had never passed; before/after measured as exit 1 with 0 lines → exit 0
  with the PASS verdict. Committed `25dc443e44a`.
- impl: Added the step-based system spec, authored mirror, plan, guide
  section, and this lane state plus the lane feature-expert skill.
- verify: Static quality, direct-env, layout/hygiene, conflict, and
  changed-file/file-count guards run against committed content. Runtime,
  docgen, and sspec-maintain deferred — see TEST_BLOCKED above.
- verify: Bootstrap attempted so the lane could be executed honestly; blocked
  by the receipt/planner circularity recorded above. Seed symlink removed
  afterward so no guard can silently run against the Rust seed.
