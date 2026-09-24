# Windows Full Bootstrap and Toolchain Suite — Feature Requirements

## Selection

Selected option: **F1 — Strict Incremental Phase Promotion**.

## Requirements

- REQ-001: Resolve the current jj conflicts without losing unrelated user or agent work, then freeze an isolated Windows bootstrap lane at an exact source revision.
- REQ-002: Run the canonical MSVC `--full-bootstrap --stop-after-stage2 --mode=dynload` trust-root command, producing Stage 1 evidence and an admitted Stage 2 binary in an isolated absolute output/cache location.
- REQ-003: Bind every phase subject to its absolute path, SHA-256, source revision, parent compiler, environment/toolchain identity, supported commands, logs, and admission receipt; missing, stale, mutable, symlinked, or cross-generation evidence fails closed.
- REQ-004: Verify the exact Stage 2 compiler and interpreter, run supported tools in interpreter mode, build native tool binaries, and exercise primary features with behavioral or protocol oracles before publication.
- REQ-005: Publish the exact passing Windows Stage 2 head to `main` using linear jj history and narrow push semantics; never publish a failing phase as passing or absorb unrelated work.
- REQ-006: Produce a typed planner admission receipt from the exact admitted Stage 2 compiler and use it to build/verify Stage 3; publish only after its phase-scoped compiler/interpreter/tool gates pass.
- REQ-007: Produce a fresh typed Stage 4 receipt from the exact admitted Stage 3 compiler, build the full CLI, and verify the exact unchanged Stage 4 binary with post-bootstrap and essential-tool gates.
- REQ-008: Verify `check`, MCP/LSP, SPipe plugin and docgen, DevHub, Caret, IDE, T32 MCP/CLI, and representative primary workflows against the exact admitted phase/candidate applicable to each gate.
- REQ-009: Re-fetch and compare `main@origin` before each publication, linearly rebase relevant fixes, preserve concurrent lanes, and rerun only evidence invalidated by source or artifact drift.
- REQ-010: Deploy only the admitted Stage 4 Windows candidate locally, atomically select one immutable generation, retain pre/post/deployed hashes, run post-deploy smokes, and prove authorized rollback with a receipt.
- REQ-011: Use the protected SPipe self-review admission workflow for every protected publication; an author GitHub `APPROVED` review is forbidden and cannot be substituted.
- REQ-012: Preserve the fixed bootstrap readiness Gate 1–6 contract and keep unavailable native/QEMU/external-host rows open or blocked with an owner, retained evidence, and exact resume command.
- REQ-013: Stop after three distinct fix/verify cycles for a failure, never rerun unchanged green evidence or an identical failed command, and record every remaining blocker precisely.
- REQ-014: Keep research, requirements, architecture, design, plans, executable specs, generated manuals, guides, expert wiki entries, workflow skills/commands, bug records, and must-check ledger rows synchronized with the implemented contract.
- REQ-015: Every eligible build must use a stable incremental cache and retain a positive reuse receipt; a cold rebuild is not accepted as incremental and is run only when an explicit release/trust rule requires it.

## Traceability Source

These requirements refine AC-1 through AC-24 in `.spipe/windows_full_bootstrap_toolchain_suite/state.md` and the selected F1 option.
