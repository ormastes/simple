<!-- codex-research -->

# Release Process Hardening Requirements

**Status:** Selected
**Selection source:** User-supplied research document and its “Executive decision”
**Research:** `doc/01_research/infra/release/simple_spipe_release_branch_tag_test_repair_bootstrap_scheduling_hardening_2026-08-26.md`

## Goal

Simple and Spipe shall provide one policy-driven software-release workflow for stable and prerelease channels that isolates every mutating session, derives every product version from one authority, admits reviewed beta bug-fix backports, builds immutable candidates once, and promotes exact admitted artifacts under generated, parity-checked operator and LLM guidance.

## Requirements

- **REQ-001 — Canonical version authority:** `release/version.sdn` shall be the sole editable product-version authority. Every declared version projection shall be deterministically rendered or checked, and version drift shall fail closed.
- **REQ-002 — Version grammar:** New release identities shall use SemVer `X.Y.Z` or lowercase numbered `X.Y.Z-alpha.N`, `X.Y.Z-beta.N`, and `X.Y.Z-rc.N`. Tags add exactly one `v` prefix. Legacy irregular identities shall remain immutable history and shall not validate as new releases.
- **REQ-003 — Compatibility-aware bumps:** Release policy shall record public API, compiler ABI, bootstrap protocol, package format, SCV schema/wire, DevHub provider, Spipe skill/plugin, release-manifest, and bootstrap-receipt compatibility dimensions and reject a version bump smaller than the declared compatibility change requires.
- **REQ-004 — Isolated mutation sessions:** Every release, beta, patch, hotfix, and backport mutation shall be bound to one unique session ID, one owned `work/*` branch/bookmark, one physical worktree/workspace, an exact base SHA, and a private output/cache overlay. The main worktree shall be read-only for authoring.
- **REQ-005 — Protected-ref authority:** `main`, `release/*`, `candidate/*`, recovery refs, and `v*` tags shall be updated only by their declared integration/release authorities using compare-and-swap or create-once operations. Ordinary release tools shall not expose raw protected-ref mutation.
- **REQ-006 — Beta release lines:** Beta preparation shall operate on an exact protected revision for `release/X.Y` and produce `X.Y.Z-beta.N` metadata. A new source, policy, support, or required configuration revision shall create a new candidate attempt or beta number instead of mutating an existing identity.
- **REQ-007 — Reviewed beta bug-fix backports:** Beta maintenance shall accept only caller-identified reviewed bug-fix commits. Admission shall verify and record source commit SHA, stable change/work ID, target release line, adaptation reason, exact target base, review identity, and renewed focused evidence. Unrelated feature commits, ambiguous source refs, stale targets, and direct cherry-picks into protected refs shall be rejected.
- **REQ-008 — Immutable candidate:** Candidate creation shall bind version, attempt, exact commit, source tree, policy, version manifest, toolchain, support matrix, build graph schema, creator, and evidence identities. Candidate refs and admitted artifact identities shall be create-once.
- **REQ-009 — Promote, do not rebuild:** Release promotion shall consume the exact admitted candidate artifacts and their digests. Promotion shall never rebuild, rewrite versions, use a moving artifact identifier, or substitute a seed, committed binary, older binary, or source-only package for a required artifact.
- **REQ-010 — Signed exact tag plan:** Promotion shall require a signed annotated SemVer tag plan targeting the exact admitted commit and shall push exactly one tag ref. Lightweight/unsigned tags, `git push --tags`, tag movement, deletion, reuse, or target mismatch shall be rejected.
- **REQ-011 — Withdrawal and correction:** Operational rollback shall redeploy a previous admitted release. Withdrawal shall retain tag, assets, and audit history. Corrections shall receive a new beta, RC, or patch identity; ordinary workflows shall not rewrite published release identity.
- **REQ-012 — Simple release command surface:** The shipped Simple release CLI shall provide focused version render/check/bump, beta preparation, backport verification, candidate creation/status, promotion dry-run/verification, and withdrawal planning with typed results and actionable failure reasons.
- **REQ-013 — Spipe plugin surface:** The Spipe plugin shall declare compatible release/session/candidate schemas and expose guarded CLI/MCP/skill operations for the workflow. Mutating operations shall require session/workspace, expected base/target SHA, expected policy hash, and operation capability; irreversible promotion remains approval-gated.
- **REQ-014 — Projection parity:** One canonical semantic release-skill source shall project into affected Claude, Codex, Gemini, pipe, embedded Simple, CLI/MCP help, and human guidance. A parity gate shall reject stale hashes and unsafe legacy phrases/commands.
- **REQ-015 — Exact verification:** Executable SSpec and focused implementation tests shall cover successful beta preparation/backport/candidate/promotion planning and rejection of malformed versions, stale projections, unrelated or unreviewed fixes, mutable candidates, fallback/rebuild promotion, unsafe tags, destructive rollback, main-worktree mutation, and projection drift. Release admission additionally consumes one successful whole test run.
- **REQ-016 — Trunk/release convergence:** While a beta or bootstrap qualification lane is active, a scheduled read-only discovery job shall occasionally compare the exact heads and reviewed bug-fix inventories of `main` and `release/X.Y`. It may propose only exact commits; it shall never cherry-pick or push automatically. A selected fix from `main` is integrated into the release line through a private backport session, and a fix first developed on `release/X.Y` is integrated forward into `main` through a private forward-port session. Each direction requires review, renewed result-revision evidence, protected integration authority, compare-and-swap, and a divergence receipt. `main` remains the development trunk and shall never be reset, repointed, or made to track a release branch.

## Traceability

The system-test plan maps every REQ identifier to executable scenarios and the mirrored operator manual. The implementation design maps each requirement to a pure-Simple owner, policy/schema field, or generated documentation projection.
