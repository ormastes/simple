# Item 3: typed collections and query optimizer

## Objective and selected scope

User requested further research, updated plan/design documents, concrete modern
SSpec acceptance tests, TDD implementation, and parallel isolated worktrees on
the release branch. The selected contract remains REQ-001–011 in
`doc/02_requirements/feature/collection_planner.md` and NFR-001–007 in
`doc/02_requirements/nfr/collection_planner.md`.

Status: **IN PROGRESS; verification is incomplete; no release admission.**

## Session ownership (2026-10-03)

- Session: `01a0fedc-f802-7af2-ab5b-a5c6abe85984`, merge/review owner `/root`.
- Integration worktree: `C:/dev/simple-item3-dev-20261003`.
- Work branch: `work/item3-dev-20261003`; target: `release/1.0`.
- Refreshed base and expected target: `cb2f783acf0ea22e8da54ff0d8d18b4fb14c816c`.
- Research, specifications, and planner agents have separate sibling worktrees
  and `work/item3-{research,spec,planner}-20261003` branches. Their commits are
  integrated explicitly; unrelated items 1/5 and bootstrap work are preserved.
- Each worktree retains a local Git ownership receipt. No protected ref is
  updated directly, and no release tag or publication is authorized here.

## Evidence boundaries

The test plan owns CP-001-A through CP-011-C: 33 full-scope acceptance scenarios.
CP-GUARD scenarios separately exercise the real advisory selector and explain
API. A selector result does not prove extraction, lowering, generated artifact
execution, cross-engine semantic parity, or NFR compliance.

`C:/dev/simple/bin/simple.exe --version` reports a Rust bootstrap seed.
The inspected WSL snapshot `/root/simple-build/build/phase_snapshots/phase1_1790916939/simple`
also reports a Rust seed. Neither is used for normal test verification.
The Windows LLVM Stage 2 compiler under
`C:/Users/user/.simple/worktrees/simple-windows-phase2/build/bootstrap-llvm80/stage2/x86_64-pc-windows-msvc/simple.exe`
identifies itself as `simple-bootstrap 1.0.0-rc.1`; its help exposes compilation
only, not `test`, `check`, or doc generation. Native attempts through it are
diagnostic, unadmitted evidence, not full runtime acceptance.

The native bound-regression build first rejected missing SCV compile-event
journal admission. Retrying once with the prescribed cold-inventory setting
timed out after 120 seconds without an executable. The test-first commit
`944e1fe7644` precedes source fix `8ab6c4d7bd1` in the planner lane, but neither
attempt establishes semantic RED or GREEN. The tracked diagnostic report is
`doc/09_report/collection_planner_bound_tdd_2026-10-03.md`.

The guard now rejects static size or admitted profile size exceeding a known
hard bound before attributes can authorize an alternative. Exact bounds and
unadmitted profiles retain their existing semantics. Independent source review
found no P0/P1; runtime correctness remains unverified. No full REQ is closed
by this focused guard.

## Remaining work and stop conditions

1. Obtain an admitted self-hosted CLI and execute the test-first regressions;
   preserve actual RED and GREEN logs. A compiler failure is not a RED test.
2. Connect typed registry resolution, HIR extraction, proof construction,
   physical selection, MIR lowering, and generated artifact execution using the
   architecture/design contract. Retain exact original-region fallback.
3. Implement the remaining collection, generic-index, typed-column, diagnostics,
   profile, and explain requirements using the concrete system-test matrix.
4. Execute all retained semantic, backend, host and NFR gates. Generate the SSpec
   manual with the actual tool; authored documentation is not generated evidence.
5. Run the required compiler/lib/MCP/LSP and runtime/native smoke checks, review
   the exact owned diff and live PR comments, then land through a release-line PR.

Do not mark this objective complete because the documentation or selector guard
is ready. At most three fix/verify cycles are allowed per feature; do not repeat
already passing checks without changed code or new failure evidence.
