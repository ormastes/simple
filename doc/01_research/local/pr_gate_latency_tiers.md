<!-- codex-research -->
# PR gate latency and tiers: local research (2026-09-23)

## Scope and existing policy

The active `spipe-vcs-v3-main` ruleset requires two GitHub Actions contexts: `Code Idiom & Structural Ratchet Gates` and `SPipe Self Review Admission`. Its live `strict_required_status_checks_policy` is `false`, while `.github/rulesets/spipe-vcs-v3-main.json` and the admission broker require `true`. The broker checks that bit before publishing its required check, so no PR-local change can make admission appear while the live drift remains.

`repo-hygiene.yml` already keeps the Code Idiom job name stable and has a fail-closed, receipt-independent docs-only classifier. It skips many source-scoped steps but still runs root placement, guard wiring, submodule shape, plan acceptance, and several unconditional checks. The signed local-CI receipt route is separate; the base manifest declares 27 idiom rows, 24 with unbounded `*` inputs, so generic test-only or small-code skipping is not yet justified by the manifest. Unknown, mixed, rename, policy, API-failure, and changed-file-count-mismatch cases must take the full route.

## Measured delay

Live GitHub API snapshots showed 503–523 queued runs with only five in progress. A sampled required idiom job waited 2h20m39s for a runner, then completed successfully in 3m25s. This makes scheduling/fanout the dominant delay; optimizing steps inside that job alone cannot make a queued required check start. There are 47 workflows, 31 triggered by PRs and 37 by pushes. Several already have path filters; `cache-branch-ci` is an optional broad branch-push trigger and the self-review broker creates invalidation runs on multiple events. Any fanout change must preserve release/security evidence.

## Compile lane and limitations

`build-binaries.yml` has a Linux Stage 2 CLI native build, but some follow-up smoke commands mask failures with `|| true`/`|| echo`; it is not currently a trustworthy mandatory compile-and-run verdict. `check-aot-smoke.shs` is an existing hard build-and-run oracle, but can be slow (900-second timeout). The `Core + MCP Guard` invokes the Rust seed for `check`; that alone does not prove a pure-Simple self-hosted binary. A new minimum compile context should first prove a hard native build plus execution on a PR, with a stable unique check name, before replacing existing required contexts.

## SPipe setup gap

The configured legacy common mount `.spipe/spipe` exists, but its expected common `wiki/index.md` and setup/ownership leaves are absent in this checkout; `doc/00_llm_process` contains only `release_playbook.md`. `sb/doc/00_llm_process/knowledge_registry.sdn` has no `.github/**` route for this feature. This is a research/setup gap, not authorization to infer a missing SPipe rule. Existing checked-in gate/operator docs and workflows were used for this bug investigation.
