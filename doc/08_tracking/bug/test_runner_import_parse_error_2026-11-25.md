# Test runner and imported-module parse errors: no swallow; seed/pure parser divergence (2026-11-25)

Status: verification-pending (lane trparse, `work/test-runner-parse-fail-20261125`)

## Report
PR #11363 fixed `src/lib/nogc_sync_mut/container/linux_installed_provider_inventory_v1.spl`.
`compiler.core.parser` (`parse_module_silent_checked`) rejected it with
`E0002 unexpected token ':'` at 310/332. A spec that imported the module still
passed. The suspicion was that the runner or loader swallows parse errors in imported modules.

## Findings (seed `bin/simple.exe`, 2026-11-19 build, runner from release/1.0.0)
1. **The runner does not swallow loader parse errors.** A spec that imports a module the
   executing parser cannot parse fails as expected. The runner exits 1 and reports
   `outcome=ERROR`, `Results: 1 total, 0 passed, 1 failed` and
   `error: compile failed: parse: in ...\broken_mod.spl: Unexpected token: expected identifier, found Assign at line 5, column 8`.
   We did not find an `if let Ok` swallow on this path. The JIT demotion message
   (`[engine-demotion] reason=jit-compile-error`) is followed by an interpreter failure. It is not followed by a pass.
2. **Root cause of the PR #11363 case is parser divergence.** The rejected form
   puts `else: <value>` on an indented continuation line of an `if` expression:
   ```
   r = if n > 0:
       1
       else: 2
   ```
   The Rust seed parses this form. `pick(1)` returns 1 and both the import-only and call specs pass.
   The JIT demotion seen there was only `jit-bail:no-main-fn`. `compiler.core.parser`
   rejects the same form with E0002. Code that runs fine on the seed is therefore
   unparseable for the pure-Simple toolchain (lint, LSP, self-hosted compile).

## Census (same `= if ...:` / deeper `else: <value>` shape, src/**, excl. vendor)
- `src/compiler/80.driver/driver_entry_closure_core.spl:2779`
- `src/compiler/80.driver/smf_group_object_adapter.spl:162`
- `src/lib/hardware/rv64gc_rtl/imac_protected_core.spl:306`
- `src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:1264`

These are unconfirmed candidates. On this host `compiler.core.parser` cannot be run
under the stale seed, which fails with a private-fn visibility error in `_AstExpr/nodes.spl`,
so the pure parser's verdict on each site still needs checking.

## Fix / guard
- Regression spec: `test/01_unit/app/test_runner/import_parse_error_fails_spec.spl`.
  It runs `bin/simple test` on
  `test/fixtures/test_runner/parse_fail/imports_broken_fixture.spl`, which imports the
  deliberately broken `broken_mod.spl`. The spec asserts a non-zero exit, `outcome=ERROR`, and a message that names
  `broken_mod.spl` and `line 5`. It was green on first run because the reported swallow does not
  reproduce. That is recorded here so the result is not read as a fake red.
- Open: unify the two parsers on this form. Either make the seed reject it or make
  `compiler.core.parser` accept it, with an owner decision on the grammar. Then
  re-check the census sites. No seed change was made and the seed was not rebuilt.
