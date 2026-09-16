# Text-wide branch coverage lacks a retained all-owner closure receipt

## Status

Partially resolved infrastructure; text/i18n/rendering closure remains open and blocks the requested aggregate 100% branch-coverage claim.

## Evidence

- `src/compiler/10.frontend/core/ast_coverage_inventory.spl` already walks the canonical flat AST and emits zero-count decision/condition rows, including rows never executed.
- `src/lib/nogc_sync_mut/test_runner/test_runner_coverage.spl` pre-registers the compiler manifest and merges child-process outcomes; `test_runner_coverage_aggregation_spec.spl` proves an untouched decision remains in the denominator and that per-owner `@cover 100%` fails at 50% or missing data.
- `test/01_unit/compiler/frontend/flat_ast_child_ownership_spec.spl` proves deterministic inventory, path escaping, deduplication, nested expression coverage, and marked-manifest shape.
- Focused interpreter evidence passed on 2026-08-26: 4/4 aggregation examples and 7/7 flat-AST inventory examples.
- No retained receipt yet scopes every text/i18n/Draw IR/Engine2D/Engine3D owner, and Rust/C/SIMD/GPU branches require their native coverage tools plus a merged owner ledger.

## Required fix

Use the existing compiler manifest for Simple owners and add the missing text/i18n/rendering owner list, source/config hashes, per-owner outcome receipt, and reviewed-unreachable ledger. Merge Rust/C coverage only with exact file/profile identity and vendor exclusions. Forced SIMD/GPU rows additionally attest the active backend; source compilation alone is not branch execution.

## Owner and unblock condition

- Owner: text/i18n integration lane, with compiler coverage/tooling and backend owners.
- Unblock: one retained aggregate names every owned file and branch denominator, rejects missing/stale owners, shows 100% reachable outcomes or reviewed exclusions per owner, merges native Rust/C evidence, and binds forced backend identity.
