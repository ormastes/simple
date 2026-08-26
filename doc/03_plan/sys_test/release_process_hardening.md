<!-- codex-design -->

# Release Process Hardening System Test Plan

## Spec and manual

- Executable: `test/03_system/app/release/feature/release_process_hardening_spec.spl`
- Manual: `doc/06_spec/03_system/app/release/feature/release_process_hardening_spec.md`

## Requirement mapping

| Requirements | Scenario evidence |
|---|---|
| REQ-001..003 | canonical stable/beta parsing, channel agreement, projection drift, compatibility bump rejection |
| REQ-004..005 | isolated work session accepted; main workspace/direct protected ref/stale target rejected |
| REQ-006..007 | beta line and reviewed fix backport accepted; feature/unreviewed/ambiguous/wrong-line/stale evidence rejected |
| REQ-008 | exact candidate accepted; missing fact, ref mismatch, and attempted mutation rejected |
| REQ-009..010 | admitted exact promotion accepted; rebuild/fallback/moving digest/unsigned/lightweight/all-tag plan rejected |
| REQ-011 | redeploy/withdraw accepted; delete/move/reuse rejected |
| REQ-012..014 | CLI help/contracts, plugin schema/capability, and model projection parity |
| REQ-015 | focused suite and final release-bound whole test evidence |

## Execution order

Run each unchanged passing gate once: focused unit/spec checks, CLI rejection fixtures, Spipe plugin build/parity, docgen, `sspec-maintain scan`, lint/duplicate/runtime guards, then the single final `bin/simple test test --whole --mode=interpreter`. Stop after three distinct fix/verify cycles or repeated identical no-progress failure.

## Unsupported external rows

Live GitHub ruleset mutation, real signing, protected tag push, immutable GitHub publication, and registry publication require explicit external authority and are not executed by this implementation lane. Their policy/plan rejection behavior remains testable; they cannot be counted as live PASS.
