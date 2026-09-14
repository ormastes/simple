# Release refused 2026-09-14 — beta required row `x86_64-unknown-linux-gnu` is `blocked`, and the candidate/release CI route has never succeeded

Session: `work/release-2026-09-14`, worktree `.claude/worktrees/agent-ab81388b5fde969c4`,
base `a7a19a52182` (= `origin/main` at start). Host: macOS aarch64.
Directive: "do local and remote release" (local release + tag push + GitHub release).

**Verdict: NO tag was created and NO GitHub release was published.** The refusal comes
from the release admission contract itself (`doc/07_guide/infra/software_release.md`,
`release/support.sdn`), not from operator caution. The guide states bug/support
requirements have "no waiver", so the user's push authority cannot substitute for a
missing required-platform receipt.

## Identity that a release would have had to use

- `release/version.sdn` canonical semver: **1.0.1-beta.1**, line `1.0`, channel `beta`.
- `git tag --list 'v*' | sort -V | tail`: `v0.9.8`, `v1.0.0-RC`, `v1.0.0-beta`,
  **`v1.0.1-beta.1`** (annotated; `git cat-file -t` = `tag`), `vgate-probe-004312`.
- `gh release list`: **`v1.0.1-beta.1` is already published** (pre-release,
  2026-09-06T23:49:50Z). Published identity is immutable and tags are immutable by the
  `spipe-vcs-v3-version-tags` ruleset, so `v1.0.1-beta.1` must not be reused or moved.
- Therefore any new work requires a **new** identity: **`1.0.1-beta.2`**.
  `release/version.sdn` still reads `1.0.1-beta.1` and is stale relative to what is
  published; a beta.2 would need a `version-bump` + projection PR first.

## Checker verdicts (verbatim)

Run with the seed's `run` (`bin/simple run src/app/release/main.spl <cmd>`) because the
bootstrap CLI has no `release` subcommand. The seed is used here only to *execute a pure-Simple
checker*, never as release evidence.

```
Release version-check: PASS
```

```
{"output_version":"simple-release/v1","command":"release support-check","status":"ok","channel":"beta",
 "required_support":[{"target":"x86_64-unknown-linux-gnu","tier":"tier_1","runner":"ubuntu-latest",
   "bootstrap":"full","whole_tests":"required","status":"passed"}],
 "support_matrix":[{"target":"x86_64-unknown-linux-gnu","tier":"tier_1","runner":"ubuntu-latest",
   "required":true,"availability":"supported","bootstrap":"full","whole_tests":"required",
   "status":"blocked"},
  {"target":"aarch64-unknown-linux-gnu","tier":"experimental","runner":"self-hosted",
   "required":false,"availability":"experimental","bootstrap":"full","whole_tests":"required",
   "status":"experimental"}]}
```

```
{"output_version":"simple-release/v1","command":"release candidate-check","status":"rejected",
 "reason":"candidate version is invalid"}
```

```
{"output_version":"simple-release/v1","command":"release promote-check","status":"rejected",
 "reason":"release mutation requires a session id and workspace"}
```

## Why this is a hard blocker, not a paperwork gap

1. **The one required beta target is `blocked`.** `release/support.sdn` declares exactly one
   `required: true` row per channel (`check_single_job_coverage` enforces one), and for `beta`
   that row is `x86_64-unknown-linux-gnu`. The live support matrix reports it
   `"status":"blocked"`. The guide: "Only actually executed required rows may say `passed`; a
   missing required receipt blocks admission."
2. **This host cannot supply that row.** The session host is macOS aarch64. The binary the
   bootstrap lane (F74) is deploying is `aarch64-apple-darwin-macho`, which is **not a declared
   row at all** in `release/support.sdn`. The guide forbids exactly this substitution: "No lane
   may substitute a seed, source-only, or foreign-target fallback artifact for a missing native
   result." A macOS whole-suite PASS is genuine evidence for an undeclared target; it is not the
   required Linux receipt.
3. **The CI route that *would* produce that row has never worked.**
   - `gh run list --workflow=candidate.yml -L 5`: five most recent runs are **all
     `completed failure`, each `0s`** (latest 2026-08-27). There is no successful
     `Build and qualify immutable candidate` run, hence no `simple-release-candidate/1` /
     `simple-release-admission/1` evidence in existence.
   - `gh run list --workflow=release.yml -L 5`: **all `completed failure`**, including run
     `34067963746` for tag `v1.0.1-beta.1` itself (4h53m52s, failure, 2026-09-06).
   - Consistent with that, **`gh release view v1.0.1-beta.1` lists zero assets** — the published
     beta.1 release carries no admitted artifacts. So the already-published beta.1 did not go
     through a completed promotion either.
4. **No admitted candidate exists to promote.** `promote-check` requires "an admitted candidate
   identity and exact commit" plus "exact matching artifact/evidence manifests". Nothing has ever
   been admitted (point 3), so promotion has no input and correctly rejects.
5. The guide's own § *Current verification boundary* already records this state: "The exact
   release lineage still lacks admitted Stage 3 and Stage 4 receipts and one clean release-grade
   `bin/simple test test --whole --mode=interpreter` PASS. No signed beta tag, immutable candidate
   publication, or byte-identical npm publication receipt exists." That paragraph is still
   accurate, with the one correction that a tag named `v1.0.1-beta.1` *was* subsequently pushed
   and a GitHub release published — asset-less, over a failed `release.yml` run.

## Release-bound whole-suite test: not run, dependency never arrived

The directive bound the release to ONE `bin/simple test test --whole --mode=interpreter` PASS on
the self-hosted full-CLI binary being deployed by the F74 bootstrap lane.

- `bin/simple` resolves to the **Rust seed** (`target/bootstrap.generations/502da3d0…/simple`),
  which prints `WARNING: this Rust-built Simple binary is a bootstrap seed only` and reports
  `Simple Language v1.0.0-rc.1`. The seed is bootstrap-only and is not release evidence.
- `bin/release/aarch64-apple-darwin-macho/simple` is dated **Sep 7 16:38**, i.e. the pre-existing
  artifact, not a fresh F74 deploy.
- Last F74 status lines observed:

  ```
    (pid 67477 = stage2-admitted compiler, 58 min CPU, 23%, compiling src/app/cli/bootstrap_main.spl
     -> stage3/aarch64-apple-darwin/simple). The resume path pins --threads 1, so 60 min was an
    under-estimate, not a hang. NOT killed: killing a live build is exactly what cost the last two lanes.
  ```

  The lane is still building **Stage 3**; Stage 4 / full-CLI relink has not started.

Even had it landed, per §2 above a macOS-arm64 PASS could not admit this release. It would be
recorded as evidence for an undeclared target.

## What a legitimate `1.0.1-beta.2` needs

1. Repair `.github/workflows/candidate.yml` so it completes on `ubuntu-latest` (its runs fail at
   0s, i.e. before doing work — triage that first). Without a green candidate run there is no
   admitted artifact for any channel.
2. `version-bump` to `1.0.1-beta.2` and land the 17 `projections:` from `release/version.sdn`
   through a PR (protected `main`, PR-only).
3. Create the create-once candidate ref, let `candidate.yml` build and qualify the required
   `x86_64-unknown-linux-gnu` row with full bootstrap + whole-test receipts.
4. Obtain `spipe-review-admission/1` (or the documented owner-attested fallback), then
   `candidate-admit`, then `promote-check`, then let `release.yml` sign the single tag and attach
   the admitted assets unchanged.

Steps 3-4 cannot be performed from this macOS host; they are CI-side.

## Raw logs

`build/release-evidence/{support-check,candidate-check,promote-check}.log`
and `candidate-check.json.log` (untracked; session-local).
