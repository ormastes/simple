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
- Only when that verifier mechanism is unavailable may owner ID `2378857` explicitly dispatch `authority_class=owner_attested_actions` from trusted `main` with `NO-VERIFY:OWNER-PROOF`. The dedicated `owner-convergence-admission` environment permits its own reviewer while release/npm protections remain unchanged. The eight-hour receipt is long enough to wait behind full Stage 2/3/4 qualification, declares `verification_performed=false` and `github_pr_approval_claimed=false`, binds exact run/workflow/config/environment/rulesets/PR/parents/candidate/manifest/ports/checks, retains unavailability proof, and is Actions-attested. Candidate admission downloads the exact run/artifact/digest and verifies trusted-main signer workflow/digest/ref with self-hosted runners denied, then separately inspects authenticated certificate identity fields. Immediately before admission it re-resolves exact live main/release/candidate refs, environment, rulesets, configuration, trusted workflow, and expiry, so the longer queue allowance cannot survive protected-state drift. Forward-port validation is authority-specific: external mode requires the exact broker App check, while owner mode requires null broker identity, owner authority, false verification/approval claims, and the exact required checks, including for an empty port set. Same author/merger is allowed only on this fallback; normal external-broker mode retains inequality.
- GitHub forbids a PR author from submitting an `APPROVED` review on their own PR. Protected PR integration therefore uses the required `SPipe Self Review Admission` check instead of provider Approve; it never claims GitHub or independent approval. Explicit `self_attested` PASS with zero P0/P1 is user-authorized but is not authenticated independent review. The trusted default-branch workflow resolves and re-resolves repository, protected target and normalized ruleset digest, head, base, merge-base, and diff, then emits a ten-minute check. Ordinary code/text is default allow absent an external operator deny/constrain. Exact scopes are `code`, `text`, `file`, `directory_files` (immediate), and `directory_recursive` (descendants); deny wins, rename covers old+new, delete old, copy new, and traversal, aliases, symlink, submodule, non-UTF-8, and actual secrets fail closed.
- On invalidation or rejection, follow the reported reason: state drift/expiry requires a new exact-head high-effort review and dispatch; a deny requires external policy-owner action or an eligible independent route; uncovered constraints require reducing the diff or a new exact constraint; unsafe/secret material must be removed (and exposed credentials rotated) before a clean head is reviewed. Never retry with author `APPROVED`, a stale check, or weakened candidate/release/publication authority. The generic Actions App trust risk is explicitly accepted and is not an independent boundary. Candidate authority accepts only `spipe-review-admission/1`; release-environment approval remains separate.

## Verification

Trace requirements to real tests, run focused repair until clean, then run one clean whole-suite confirmation. Generated/manual operator docs and model skills must agree before release. A local dry-run is not live server, signing, or publication proof.
