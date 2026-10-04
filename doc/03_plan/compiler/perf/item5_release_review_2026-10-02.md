# Item 5 release destination review

Status: prepared review lane; no protected branch updates or backports performed.

Release worktree: C:/dev/simple-item5-release-review-20261002.
Owner/session: Codex root / item5-release-review-20261002.
Work branch: work/item5-release-review-20261002.
Target: release/1.0.
Base/expected target: acaaef9906ecd16b25ec5d9c2a0b6eff5be1b92d.

This sparse isolated lane began with read-only comparison and now holds a
delegated bug-fix authoring change. Full feature implementation remains on
owned main-based work branches until release scope is resolved. The user's
request for release-branch work does not justify treating full new features as
already-reviewed maintenance fixes. The selected bug-fix lane must obtain real
tests and exact-head review before release integration, with renewed target
evidence and main/release provenance. A full release-target feature lane needs
an explicit scope decision and all retained item 5 gates.

No branch push, PR merge, tag or publication has occurred. No qualification or
promotion receipt is inferred from creating this worktree.

## Exact source comparison

The fetched release snapshot differs from main at repeated rejection:
release returns the published original failure.error (or admission_conflict
when terminal metadata is absent); main returns cached_rejection. Therefore
the authored main-based regression's cached_rejection assertion is not patch
equivalent to release behavior. Preserve and review this caller-visible error
contract before any backport. The member-authority validation seam exists on
both branches, but a successful main test is not renewed release evidence.

## Delegated release authoring

The root delegated the two admission source/test paths and a new bug evidence
note to item5_tdd_audit. The agent authored behavioral tests first with release's
original typed repeat refusal, then added only the member-table/bounds validation.
Parent inspected the exact diff and confirmed return Err(failure.error) remains.
The worktree now contains this narrow authored bug repair, not a full feature
backport. Runtime execution and backport admission remain unproven; no commits,
PRs or protected ref movement occurred. The repeated-refusal adaptation requires
reviewed result-revision evidence rather than a patch-equivalent claim.
