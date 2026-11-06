# HIR ledger diagnostic blocked by producer ABI failures

Status: ownership repair passes native regression; full integration pending.

Frozen producer SHA256: `43f9a6fc68ac232fcb3d28b0a28ada8fba5b04f5e16326e8f122d09208671c5f`.
Fixture: `test/fixtures/compiler/hir_unit_terminal/main.spl` in the isolated
`simple-hir-unit-terminal-ownership-20261106` worktree.

The original full CLI build failed on the first unclaimed import with
`HIR completion receipt publication failed`. Source inspection found that the
unit path loads dependency HIR without claiming it but later calls the strict
terminal publisher. A newer pinned producer subsequently reproduced this with healthy controls.

Two bounded native baseline attempts retained under `build/hir-unit-terminal`:

- `before`: default LLVM backend rejected an integer constant defining void in
  SHA256 streaming methods, then exited 139. No assertions ran.
- `before-cranelift`: explicit Cranelift compiled the fixture, but execution
  reported an invalid array handle and 10 failures among 17 assertions. All
  normal claim setup controls failed and the ledger directory remained empty.
  This cannot isolate the proposed unit-ownership regression.

Both attempts used canonical process guards and private caches. Neither result
qualifies a compiler or permits replacing strict claim ownership checks.
Attempts3/4 used pinned producer `ffe83fd87c69573a1ca93e24134e46bbe754be7dff2de2f0eeefc4cf60c9037a`: unchanged baseline17 assertions/3 expected failures, then scoped fix17/0, with all14 controls healthy in both runs. The old producer ABI failures remain distinct historical failures; no fix for those is claimed here.

## Proposed ownership repair

REQ-HIR-UNIT-001: after a per-file unit has loaded HIR, completion must not
publish a terminal. A claimed target already published its transaction result;
an imported dependency was never claimed by this unit. Preserve the original
transaction cache evidence even if the subsequent load has a different cache
outcome.

REQ-HIR-UNIT-002: normal shard completion must still require an existing claim
owned by the caller, reject conflicting terminal contents, and accept an exact
idempotent repeat. Do not weaken `hir_shard_recovery_terminal`.

Wire a dedicated post-load completion helper into the streaming pipeline's
successful post-load path only. Keep transaction completion and error paths
unchanged. Native ledger controls and the five SSpec cases in
`test/01_unit/compiler/driver/hir_unit_terminal_ownership_spec.spl` cover the
ownership boundary. Full CLI compilation and compiler/MCP gates remain required
before admission; helper tests alone cannot prove bootstrap qualification.
