---
name: release
description: Prepare and promote stable or prerelease Simple releases from isolated sessions and immutable admitted candidates.
---

# Protected Simple Release

Use [the software-release guide](../../../doc/07_guide/infra/software_release.md) and `release/version.sdn` as the canonical product-version authority.

## Procedure

1. Require a prior verification `STATUS: PASS`, including one `bin/simple test test --whole --mode=interpreter` result and current SPipe/manual evidence.
2. Start an isolated release session: one `work/release/...` branch, one worktree, exact protected target SHA, and private outputs. Never author in the main worktree.
3. Render/check every declared version projection. New prereleases use lowercase numbered `alpha.N`, `beta.N`, or `rc.N`.
4. For beta maintenance, target `release/X.Y`. Admit only one caller-selected reviewed bug-fix commit at a time with source SHA, change/work IDs, review/check receipts, result SHA, exact stable patch-ID equivalence, and renewed focused evidence. Adapted patches fail closed until a separately reviewed equivalence protocol exists. Never automatically select fixes.
5. Before each candidate attempt, after a bootstrap failure fix, and before release admission, fetch once and compare exact `main` and release-line snapshots read-only. Present reviewed fix proposals; do not automatically choose or apply them.
6. Backport an approved `main` fix or forward-port an approved shared release-first fix on an isolated target-specific work branch before candidate admission. Renew evidence, record a divergence receipt, and let integration authority CAS-update the protected target. Only a `non_fix` release-specific compatibility classification with reason, owner, and expiry may remain release-only.
7. Keep `main` as development trunk; never reset/repoint it to `release/X.Y`, make it track the release line, or merge the whole release line merely to carry a fix.
8. Submit through protected compare-and-swap integration and create a new immutable `candidate/v.../aNNN`.
9. Build and qualify the exact candidate once. Required failures, stale inputs, and fallback artifacts block admission.
10. Promotion verifies exact candidate/artifact/evidence digests and prepares one signed annotated tag pushed as one exact ref. Promotion never rebuilds.
11. Ask before any push or publication. Draft, attach exact assets, verify, then publish immutably.
12. Rollback redeploys an earlier admitted release. Withdrawal preserves tag/assets/history. Corrections receive a new version.

Use `simple release version-check|beta-prepare|backport-check|candidate-check|promote-check|withdraw-check` for the pure validation boundaries.

For protected PR integration, explicitly self-attest high-capability/high-effort PASS with zero P0/P1, then dispatch `SPipe Self Review Admission`. GitHub forbids PR authors from submitting an `APPROVED` review on their own PR; this is a required status check, not provider or independent approval. Ordinary code/text is default allow absent an external operator deny/constrain, using `code`, `text`, exact `file`, immediate `directory_files`, and descendant `directory_recursive` scopes. The trusted default-branch workflow resolves/re-resolves protected target/ruleset, head, base, merge-base, and diff before a ten-minute result. If rejected or invalidated, follow the reason: state drift/expiry needs a fresh exact-head review and dispatch; deny needs policy-owner action or an eligible independent route; uncovered scope needs a smaller diff or new constraint; unsafe/secret material must be removed and any credential rotated. Never use author `APPROVED`, a stale check, or weaker candidate/release/publication authority as remediation. The generic Actions App is not an independent security boundary. Candidate admission accepts only `spipe-review-admission/1`; keep release-environment approval separate.

For `self approve`, `approve PR`, or `author cannot approve`, run `spipe self-review-guide`; this is the canonical exact-head status workflow, not provider `APPROVED`.

For the repository mutation boundary, use
`scripts/release/converge-reviewed-fix.shs` with one exact commit and its bound
`spipe-review-receipt/1`. It fetches both remote heads before creating the
private branch/worktree, emits `spipe-reviewed-fix-preparation/1`, and stops
before push or protected integration.

Never move `main` or `release/*` directly, broadly push every local tag, create unsigned/lightweight release tags, delete or move published tags, rebuild during promotion, or substitute seed/old/source-only artifacts.

Live rulesets, signing, protected pushes, and publication require explicit authority. Do not confuse a local plan PASS with a live release PASS.

## rc1 Drive Machinery Lessons (2026-10-11, v1.0.0-rc.1 on release_phase3)

Hard-won operational facts for anyone driving the protected convergence/candidate pipeline:

1. **Retry naming**: failed release attempts keep the version and increment a suffix — manifests `work/release/1.0.0-rc.1_<N>` (never rename to rc2), candidates `candidate/v1.0.0-rc.1/aNNN` (never bump `a000` series). Failed attempts teach one gate at a time.
2. **Release line must match `^release/[0-9]+\.[0-9]+$`** in `pr-admission.yml`, `convergence-checkpoint.shs`, and the review broker's base→ruleset case, unless explicitly extended. To run a release from a non-standard line (e.g. `release_phase3`): relax all three sites (main + line copies), add the branch to ruleset `spipe-vcs-v3-release-lines` conditions, and map the semver in `candidate.yml` (`case "$VERSION" in 1.0.0-rc*) release_ref=release_phase3`). Brokered PRs on both main and the line; never one side only.
3. **Image drift guard**: ubuntu runner images drop packages; when `llvm-config --libfiles` advertises archives that do not exist (e.g. `libPolly.a`), `candidate.yml` must install the dev package (`libpolly-18-dev`) before fingerprinting. Verify archives exist, don't trust llvm-config output.
4. **MAX_ARG_STRLEN**: convergence receipt accumulation with `jq --argjson` blows the kernel arg limit around ~624 manifest rows; use `slurpfile` + `$var[0]` streaming (verify with 700+ synthetic rows).
5. **Candidate refs via API only**: `git push` to `candidate/...` is ruleset-blocked; create with `gh api repos/.../git/refs -f ref=... -f sha=...`.
6. **Convergence tip race**: convergence requires a quiet ~3 min window on the release tip; on tip drift rebind a fresh manifest PR (validator prunes merged classifications, then requires exact equality with `git rev-list origin/main..<release-ref>`). Never merge-sync a manifest PR branch to chase the base — convergence requires `inventory_head..HEAD` to touch only the manifest. Merge-sync IS correct for ordinary fix PRs.
7. **Transplant clobber risk**: main-transplants can silently revert line fixes; when a fix must live on both main and the line, verify both sides after any transplant lands.
8. **`gh workflow run` prints the run URL on stdout even on success** — parse stdout for the URL, treat only HTTP/error text as failure.
9. **Fast-moving release lines lose the broker's resolve→fetch window** ("protected base advanced after provider resolution"); expect several redrive cycles and resync the PR branch between them.
10. **FreeBSD wrapper**: `--full` needs hours — wrapper timeouts 7200→14400s; guest bootstrap logs must be probed under `.simple/storage/build/bootstrap/logs/` first; host needs 4 GiB+ free *per run* for the overlay (delete stale overlays, they are 10–14 GB each); QEMU_MEM wants a `G` suffix.
11. **Main-absorption invariant**: `pr-admission.yml`/`candidate.yml` forbid the release line containing main (`release head must not absorb the main development line`). A designated main-sync line (release_phase3) must be explicitly scoped out of that check on **both** main and the line. Once main enters a release line's ancestry (via any merge), reverting cannot remove it — only a scoped relaxation or a line rewrite fixes convergence.
12. **Contaminated resyncs on hot lines**: concurrent agents may transiently repoint a release line at another ref; a PR-branch resync (`git merge origin/<line>`) silently absorbs whatever the remote tip is into the PR head. Check `git merge-base --is-ancestor origin/main <line>` before and after any resync-driven PR merge.
13. **Vendored Inkwell needs llvm-sys**: `--features llvm` seed builds resolve `llvm-sys` (110.0.4 per Cargo.lock) from `src/compiler_rust/vendor/`; vendoring inkwell without its llvm-sys tree breaks offline FreeBSD (and any hermetic) seed builds — verify the lock's llvm-sys entry exists in vendor before declaring a vendoring PR complete.
14. **Merge-parents exact-match is brittle on hot lines**: `pr-admission.yml` used to require `git show -s %P == "$base_sha $head_sha"` with the PR API's base.sha; that value goes stale the moment any other PR merges into the line before yours, and the check fails *silently* (`test` with no message). Replace with: second parent == head.sha AND recorded base.sha is an ancestor of the first parent.
15. **Broker redrive must resync every cycle**: on a fast base, "broker ok but merge missed" and "protected base advanced" both recur; resync the PR branch (merge origin/<base>) before *every* redispatch, not only after merge misses, and re-dispatch with the fresh head sha.
16. **Ruleset projection parity**: `scripts/release/github-policy.shs verify-live` (run inside pr-admission/candidate) diffs live rulesets against the checked-in projection `.github/rulesets/*.json` and fails *silently* on drift. Any ruleset condition change must update the projection on **both** main and the line in the same release window.
17. **Manifest release_ref rebinding**: when re-seeding the convergence manifest for a different release line, `manifest_step.py` must also rewrite `release_ref` — every downstream validator (`pr-admission` manifest jq, candidate projection) exact-matches it, and a stale `release/1.0` value fails silently via `jq -e`.
18. **Silent-failure triad**: `test` (no message), `jq -e >/dev/null` (no message), and `jq PROGRAM` with empty stdin (no output, exit 0!) all fail or misbehave silently in workflow steps. `jq -n` is required for constant programs; temporary `set -x` in the step is the fastest way to locate the exact failing command on GitHub runners.


