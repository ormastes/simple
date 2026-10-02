# Item 5 isolated development session

Status: IN_PROGRESS; no implementation or host certification claimed.

Owner: Codex root. Session: item5-dev-20261002.
Worktree: C:/dev/simple-item5-dev-20261002.
Branch: work/item5-dev-20261002.
Target: main, pending user clarification of release scope.
Base and expected target: e10963a3b065dde1643c777512c3988526973957.
Observed release/1.0 snapshot: acaaef9906ecd16b25ec5d9c2a0b6eff5be1b92d.

The user requested parallel isolated worktrees and release-branch work. New
feature scope must not silently become a maintenance backport. Confirm the
release destination before integrating; protected refs move through PRs only.
No release tag or publication is authorized by this session record.

## Scope

Retain all selected REQ-001 through REQ-015 and NFR-001 through NFR-007 in
runtime_optional_provider_binary_size_optimization.md. Item 5 also requires
kernel/driver layering, actual optional dependency exclusion, sealed extension
loading, failure handling, provider lifetime, and host evidence. A focused
admission repair cannot certify the whole item.

## Parallel ownership

- Root: research integration, acceptance plan, architecture/design updates,
  merge ownership, final review and evidence audit in this worktree.
- item5_research: additive research authored in
  C:/dev/simple-item5-research-20261002, work/item5-research-20261002 and copied
  into this main-based session after review. Runtime discovery was read-only.
- item5_tdd_audit: authored member-authority source/tests in
  C:/dev/simple-item5-admission-20261002, work/item5-admission-20261002;
  delegated corresponding paths in the release-review worktree, preserving
  its repeated-error contract. Both lanes remain runtime-unverified.

Preserve unrelated dirty command files in C:/dev/simple. Do not copy them here.

## Shared acceptance interface contracts

Preserve existing production interfaces. Proposed system fixture helpers:
item5_build_fixture_v1, item5_observe_process_v1, item5_inspect_link_v1,
item5_mutate_provider_v1, item5_check_evidence_v1. These names are reserved for
real artifact construction, execution observation, binary inspection, immutable
mutation and typed evidence validation respectively. Missing implementation
must fail explicitly; it must never fabricate a successful receipt.

Manual step vocabulary: Build the admitted kernel and sealed extension artifacts;
Observe registration before any capability demand; Demand the selected capability
once; Inspect retained roots and dynamic dependencies; Reject the mutated provider
before any effect; Release provider pins before closing the session; Compare
matched size and startup cohorts.

## Runtime gate

2026-10-02: C:/dev/simple/bin/simple.exe --version identifies itself as a
Rust-built bootstrap seed. bin/release is absent. This binary is not authorized
for normal test/check execution. Discover an admitted self-hosted binary before
claiming RED/GREEN or running compiler/core checks. Record a missing runtime as
an unmet gate, not a passing test or a reason to use the seed.
