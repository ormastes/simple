# Seed: module name shadows match binding in `Ok(value): value`

**Status:** Fixed 2026-11-04 on work/seed-modshadow-20261104 (seed interpreter); read-path sites renamed earlier on work/messenger-db-test-layers-20261031
**Severity:** P2
**Date:** 2026-10-31

## Symptom

On the Phase 1 seed in spec mode, when a program imports `std.common.json.value`, the module name `value` takes precedence over a match binding named `value` in `case Ok(value): value`. The program fails with `tuple index access on non-tuple type i64`.

## Evidence

- Read-path sites were renamed on work/messenger-db-test-layers-20261031.
- `git grep -c "Ok(value): value" -- src/lib` reports 517 sites across 112 files (counted 2026-10-31).

## Unverified

- Whether the same shadowing happens outside spec mode or on a rebuilt compiler.
- Whether all 517 sites are reachable from a program that imports `std.common.json.value`. The count is of text matches, not of reachable call sites.

## Root cause and fix (2026-11-04)

`match` arms scope their bindings with `enter_block_local`/`restore_block_scope_shadows`, but the `if val <pattern> = e:` / `elif val` / `while val` paths inserted structural-pattern bindings (`Ok(value)`, `Some(x)`) with a bare `env.insert`. `Env::is_local` stayed false, so the Identifier read (`interpreter/expr/literals.rs`) preferred the imported module namespace `value` over the binding. The `match` form itself never reproduced.

Fix: new `bind_block_scope_shadows` (`interpreter/block_exec.rs`) binds with `enter_block_local`; each site restores via `restore_block_scope_shadows` after the body (before `?`/loop-control), so the module is visible again after the block. Sites (structural and plain-identifier `if val NAME` arms alike): `interpreter_control.rs` (exec_if, elif, exec_while, exec_if_core x2 + 4 plain arms), `interpreter_call/block_execution.rs` (4 + 4 plain arms), and the expression-form `if val` in `interpreter/expr/control.rs` (which previously used the frame-permanent `mark_local`). An earlier `mark_local` attempt was rejected: it hid the module for the rest of the frame.

Evidence: spec `test/01_unit/compiler/interpreter/module_name_shadow_match_binding_spec.spl` (25 cases).
- Before: `/home/yoon/dev/cargo-rel100/simple-base` sha256 11088ca6962704a1d3c74115fe59006155590ec6042316cab30e39bb911225fb: `Results: 25 total, 11 passed, 14 failed`.
- After: `/home/yoon/dev/cargo-rel100/release/simple` sha256 555b8a092662093303d11ba0d7807d8611f618331e6779327ee134348cfaeec6: `Results: 25 total, 25 passed, 0 failed`.
- Nine neighbouring interpreter specs (aliased_param_writeback, array_push_loop_local_len, flat_if_chain, generator_for_in_iteration, match_arm_early_return, match_binding_*, match_expr_binding_scope, while_body_scope) identical pass counts on both binaries.

## Note on the earlier stale-close (b8982b49a81 / b4e4b552dcd)

Those commits closed this bug as stale because the `match` form does not reproduce. The `if val` / `elif val` / `while val` statement and expression forms did reproduce on the release/1.0.0 seed (14 of 25 regression cases red on sha256 11088ca6...); this record documents that fix.
