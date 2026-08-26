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
- Maintenance/beta fixes are explicit reviewed backports of exact bug-fix commits, with provenance and renewed evidence after application.
- Integrate by exact-revision CAS or a merge queue.
- Freeze a create-once candidate before builds. Build and qualify that candidate once.
- Promotion verifies the same artifact digests, creates one signed annotated exact tag, and never rebuilds or falls back.
- Ask before external pushes/publication.
- Rollback redeploys; withdrawal preserves identity; correction creates a new version.
- Missing policy, review, evidence, signer, platform, or provider state blocks the release.

## Verification

Trace requirements to real tests, run focused repair until clean, then run one clean whole-suite confirmation. Generated/manual operator docs and model skills must agree before release. A local dry-run is not live server, signing, or publication proof.

