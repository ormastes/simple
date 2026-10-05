# Module loader calls helpers outside its imported owner

Status: source repair authored; pure-Simple regression, compilation and JIT verification **UNRUN**. This repairs three observed unresolved calls, not the complete full-CLI failure set.

## Observed evidence

The live full-CLI collector emitted `[hir-fatal]` records for `src/compiler/99.loader/loader/module_loader.spl`: `unresolved name: code_bytes_len`, `unresolved name: bytes_len`, and `unresolved name: type_args_is_empty`. Evidence log:

`C:/Users/user/.simple/worktrees/simple/runtime/windows-restart-20261004/phase34-post-link4/cranelift/phase4-full-cli/owner/.build.log.tmp.34464`

The running source snapshot is under `C:/dev/simple-bootstrap-post-bool-20261004/build/scv/snapshots/scv-revision-v1-d1538026fd00d61d36804861b126f0d2f000659b7f7962393d98f12d8c4305a9/`. The product lineage receipt records source `9737d1217bc44439b56bba6c2ef16faaff51bd20`, producer SHA256 `776ce2a1b8b0f92d44e5dd70b5fac365ba96187f76cfa0ffc2c5bdcac8fdae40`, phase 2 to diagnostic phase 4, and `admitted=false`.

At read-only inspection, full-CLI owner/collector PIDs were 64728/34464; test-runner owner/collector PIDs were 37596/22612. These are timestamped observations, not permanent process identity. Their source, processes, retained caches and artifacts were not modified or restarted by this repair lane.

## Cause and repair

`module_loader.spl` imports `..loader.compiler_sffi.*`, the actual compiler context owner. The three helpers exist only in the sibling compatibility facade `compiler/99.loader/compiler_sffi.spl`, whose comments explicitly state they have no counterpart in the actual owner. They are not brought into scope by the existing import. Release base `9af9a8c0c70c4a04f6fc3a5bac7db475362854f5` retains these invalid calls.

Replace the two byte-length calls with `code.len() as i64` and `bytes.len() as i64`, and the empty argument check with `type_args.len() == 0`. These expressions preserve the compatibility helpers' exact bodies without adding a reverse facade dependency, wrappers or fallback behavior. Allocation, mapping, symbol publication and failure handling are unchanged.

## Regression and pending verification

Tests-first commit `9db11f8734e` adds `test/01_unit/compiler/loader/module_loader_mangle_owner_spec.spl`. It imports and calls the real module's `mangle_name`, checking empty arguments, concrete integer/named types and ordered multi-type symbol identities. This is not a source-string assertion or a copied implementation.

The byte-length paths remain covered by the existing loader/JIT specification surface and required compiler checks; this new test does not pretend to execute JIT allocation. Pending admitted-runtime checks include the new regression, existing loader tests, `check src/compiler`, core runtime smoke and MCP native smoke. No RED/GREEN execution, generated test evidence, runtime admission or complete full-CLI recovery is claimed. Other observed HIR failures require separate fixes.
