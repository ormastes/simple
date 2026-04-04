<!-- codex-design -->
# Implemented Qualified Features — Parallel Audit Agent Tasks

**Feature:** `implemented_qualified_features_parallel_audit`
**Date:** 2026-04-04

## Scope

This plan covers the README items that are implemented, but should stay qualified rather than being marketed as fully complete:

- `m{}` / `loss{}` / `nograd{}`
- LLVM support
- GC and no-GC runtime families
- shared UI testing across web and TUI-web surfaces
- remote baremetal execution

The goal is to replace vague qualifier language with evidence-backed wording and explicit limits.

## Task Split

### Task 1: Math blocks and editor-backed usage

- Verify parser, evaluation, rendering, and editor-tooling evidence for `m{}`, `loss{}`, and `nograd{}`.
- Separate the implemented syntax/runtime surface from the broader deep-learning workflow story.
- Produce exact wording for:
  - what is implemented
  - what remains evolving or scoped

### Task 2: LLVM support audit

- Verify which LLVM paths are real and currently usable.
- Distinguish:
  - backend/codegen implementation
  - external LLVM tool dependence
  - host/toolchain assumptions
- Produce a support matrix for compile, link, cross-target, and bootstrap-adjacent paths.

### Task 3: Runtime family completeness audit

- Map GC and no-GC runtime families by execution path.
- Distinguish interpreter, native, loader/SMF, and baremetal coverage.
- Identify where the runtime families are both present, and where completeness still varies.

### Task 4: Shared UI testing surface audit

- Verify the shared UI test client and protocol layer.
- Confirm the evidence for shared testing across web backend and TUI web proxy.
- Explicitly reject any wording that implies one finished unified UI application layer unless supported.

### Task 5: Remote baremetal execution audit

- Verify which remote baremetal lanes are actually proven.
- Separate:
  - real execution lanes
  - host-dependent or board-dependent lanes
  - broader claims that would overstate end-to-end coverage
- Produce a lane matrix with proof references.

## Deliverables

Each task should produce:

- one focused audit note under `doc/report/`
- one concise status row for the merged summary table
- one README-safe wording proposal

The merged summary table must contain:

- feature
- implemented core
- known limits
- proof references
- recommended README wording

## Coordination Rules

- Do not upgrade wording from qualified to complete without code and test evidence.
- If evidence is mixed, downgrade to `Experimental / partial`.
- Keep “implemented with qualifiers” reserved for features that are clearly real but not uniformly complete.
- Do not rewrite unrelated README sections while running this audit.
- Do not collapse “shared testing surface” into “unified UI layer”.
- Do not collapse “real hardware lane exists” into “all remote baremetal lanes are green”.

## Acceptance Bar

Each audited feature must have:

- source file references
- at least one test, plan, or report reference
- an explicit limit statement
- a final wording proposal that fits one README bullet

The audit is complete when:

1. all five features have evidence-backed wording
2. every qualifier is tied to a concrete limitation
3. no unproven capability remains in the “implemented and safe to advertise” section
4. the merged wording can be applied to [`README.md`](/home/ormastes/dev/pub/simple/README.md) without inventing new claims
