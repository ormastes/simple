---
name: software-release
description: General protected software-release rules for stable and prerelease channels, maintenance backports, immutable candidates, and promote-without-rebuild publication.
---

# General Software Release

Apply this skill to any software repository, adapting provider commands while preserving the trust boundaries.

## Rules

- One mutation session owns one branch and one worktree. Protected trunks, maintenance lines, candidate refs, and release tags are authority-owned.
- Keep one canonical version manifest and deterministic projections.
- Use SemVer; prereleases are lowercase and numbered.
- Maintenance/beta fixes are explicit reviewed backports of exact bug-fix commits, with stable patch-ID equivalence, provider-bound provenance, and renewed evidence after application. Adapted patches fail closed until a separately reviewed equivalence protocol exists.
- During an active beta/bootstrap lane, perform one bounded read-only comparison of exact `main` and `release/X.Y` snapshots before each candidate attempt, after a bootstrap failure fix, and before release admission. Discovery proposes reviewed fixes but never selects, applies, or pushes them.
- Prepare an operator-selected fix with `scripts/release/converge-reviewed-fix.shs`: it fetches exact remote heads first, verifies the commit-bound approved review receipt, creates a unique target-based work branch/worktree, cherry-picks only that commit, and emits a preparation receipt. It never pushes a protected ref.
- Backport selected `main` fixes through an isolated release-targeted work branch. Forward-port shared fixes developed on `release/X.Y` through an isolated `main`-targeted work branch before candidate admission. Both directions require exact commits, review, renewed evidence, a divergence receipt, and protected CAS integration; only a `non_fix` release-specific compatibility classification with reason, owner, and expiry may remain release-only.
- `main` always remains the development trunk. Never reset/repoint it to a release line, configure it to track a release branch, or merge an entire maintenance line merely to carry one fix.
- Integrate by exact-revision CAS or a merge queue.
- Freeze a create-once candidate before builds. Build and qualify that candidate once.
- Promotion verifies the same artifact digests, creates one signed annotated exact tag, and never rebuilds or falls back.
- Ask before external pushes/publication.
- Rollback redeploys; withdrawal preserves identity; correction creates a new version.
- Missing policy, review, evidence, signer, platform, or provider state blocks the release.
- Prefer a commit-bound `spipe-review-admission/1` PASS receipt from a high-capability model at high effort or above. Bind repository, PR, feature/session, the server-resolved current head, exact required checks, timestamps/expiry, and audit/review digests; a later push invalidates it.
- Only when that verifier mechanism is unavailable may the owner use the same closed receipt in `owner_attested_fallback` mode with the exact reason `no eligible independent reviewer`, owner identity, and a verifier-unavailability receipt digest. This is never an admin bypass or permission to omit checks.
- Protected PR integration uses `SPipe Self Review Admission` instead of provider Approve. Explicit `self_attested` PASS with zero P0/P1 is user-authorized but is not authenticated independent review. The trusted default-branch workflow resolves and re-resolves repository, protected target and normalized ruleset digest, head, base, merge-base, and diff, then emits a ten-minute check. Trusted PR/base/policy events reset success immediately; scheduling is backup. Ordinary code/text is default allow unless external operator JSONL denies or constrains it. Deny wins; rename covers old+new, delete old, copy new; traversal, aliases, symlink, submodule, non-UTF-8, and actual secrets fail closed. The generic Actions App trust risk is explicitly accepted and is not an independent boundary. Candidate authority accepts only `spipe-review-admission/1`; release-environment approval remains separate.

## Verification

Trace requirements to real tests, run focused repair until clean, then run one clean whole-suite confirmation. Generated/manual operator docs and model skills must agree before release. A local dry-run is not live server, signing, or publication proof.
