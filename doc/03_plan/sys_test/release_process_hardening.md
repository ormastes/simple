<!-- codex-design -->

# Release Process Hardening System Test Plan

## Spec and manual

- Executable: `test/03_system/app/release/feature/release_process_hardening_spec.spl`
- Manual: `doc/06_spec/03_system/app/release/feature/release_process_hardening_spec.md`
- CLI integration: `test/02_integration/app/release/release_cli_spec.spl`

## Requirement mapping

| Requirements | Scenario evidence |
|---|---|
| REQ-001..003 | canonical stable/beta parsing, channel agreement, repository-backed projection drift, compatibility bump rejection |
| REQ-004..005 | isolated work session accepted; main workspace/direct protected ref/stale target rejected |
| REQ-006..007 | beta line and reviewed fix backport accepted; feature/unreviewed/ambiguous/wrong-line/stale evidence rejected |
| REQ-008 | exact candidate accepted; missing fact, ref mismatch, and attempted mutation rejected |
| REQ-009..010 | admitted exact promotion accepted; rebuild/fallback/moving digest/unsigned/lightweight/all-tag plan rejected |
| REQ-011 | redeploy/withdraw accepted; delete/move/reuse rejected |
| REQ-012..014 | process-level CLI JSON isolation and adversarial routing, plugin schema/capability, and model projection parity |
| REQ-015 | focused suite and final release-bound whole test evidence |
| REQ-016 | bounded read-only convergence planning in both directions; explicit reviewed selection; no mutation; release-first forward-port to `main`; reject making `main` track the release line |
| REQ-017..021 | exact target/head/base/merge-base/diff default-allow decision; honest self-attested mode; no provider approval/permanence claim; stale/expired/retarget/ruleset/P0-P1/secret rejection; deny precedence; constraint scopes; rename old+new; symlink/non-UTF-8/traversal/quote/non-ASCII alias failure; scheduled expiry reset; bootstrap source contract |

## Execution order

Run each unchanged passing gate once: focused unit/spec checks, the process-level CLI integration spec, Spipe plugin build/parity, docgen, `sspec-maintain scan`, lint/duplicate/runtime guards, then the single final `bin/simple test test --whole --mode=interpreter`. The CLI spec must prove that `version-check` reads the canonical repository manifest and checks every declared projection; planning returns concrete escaped manifest/projection content and original hashes without writing; `version-bump-plan` requires every compatibility counter; and guarded `version-bump` rejects a main-worktree session before writing while reporting `recovery_required` and `applied_files`. Missing authority, caller disagreement, malformed options, human/JSON mixing, and beta/backport/promotion hazards all fail closed. Stop after three distinct fix/verify cycles or repeated identical no-progress failure.

## Unsupported external rows

The live GitHub policy baseline is now verified: seven repository rulesets, the
declared environments, and immutable releases pass
`scripts/release/github-policy.shs verify-live ormastes/simple`. This proves
configuration only. Real signed beta tag creation, protected publication, and
registry publication remain external release gates and cannot be counted as
PASS until exact candidate receipts exist.

The new self-review ruleset/workflow files are source projections only until
the one-time bootstrap receipts prove that the external policy DB secret was
configured, the workflow reached the default branch, both rulesets were
CAS-applied, and `verify-live` passed again. Do not infer live admission from
the pure evaluator or static workflow checks.
