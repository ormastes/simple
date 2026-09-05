# Two `cli_debug` specs import symbols that never existed anywhere in `src/`

## Symptom
- `test/01_unit/app/cli_debug/service_commands_v1_spec.spl` — 3 of 5 examples fail:
  `semantic: function 'debug_wire_v1' not found`.
- `test/01_unit/app/cli_debug/debug_service_harmony_spec.spl` — 2 of 2 examples fail:
  `semantic: function 'sdb_command_contract_v1' not found`.

Verified 2026-09-06 with the fresh seed from the worktree root:
```
B=/Users/ormastes/simple/src/compiler_rust/target/bootstrap/simple
$B run test/01_unit/app/cli_debug/service_commands_v1_spec.spl
  -> SPEC FILE VERDICT: outcome=ERROR declared>=5 executed=5 passed=2 failed=3 skipped=0 dropped=0
$B run test/01_unit/app/cli_debug/debug_service_harmony_spec.spl
  -> SPEC FILE VERDICT: outcome=ERROR declared>=2 executed=2 passed=0 failed=2 skipped=0 dropped=0
```
(`ls -la $B`: 130402384 bytes, mtime Sep 5 20:01.)

## Investigation (evidence, not a guess)

`grep -rn "fn debug_wire_v1\|sdb_command_contract_v1" src/` returns 0 hits today, matching the
lane brief. Both symbols were checked case by case:

### `debug_wire_v1` / `DebugWireV1`
`src/app/cli_debug/service_commands_v1.spl:7` imports
`use std.common.debug.contracts_v1.{DebugSessionId, DebugWireV1, debug_wire_v1}` and calls
`debug_wire_v1(...)` at line 121 — but `src/lib/common/debug/contracts_v1.spl` (the resolved
module) has never defined either name. History of that file:
- `cbf4a22305b` "feat(lib): central debug service v1 (contracts_v1 + service_v1, ...)" —
  created the module. `git show cbf4a22305b:src/lib/common/debug/contracts_v1.spl | grep
  DebugWireV1` → 0 hits: it was never there at creation.
- `314e4f1c1a5` "feat(debug,sspec-train): held-out training gate ..." — only added a
  `receipt_id` field/comment to `DebugReceiptV1`; no `DebugWireV1` touched.
- `src/app/cli_debug/service_commands_v1.spl` itself has exactly ONE commit in its history:
  `e274cd33719` "chore: merge all share-history worktree branches into main" (a single-parent
  commit, `git show -s --format='%P' e274cd33719` → one parent — a bulk file sweep, not a real
  git merge). It landed already broken and has never been touched since.
- The only other reference to `DebugWireV1`/`debug_wire_v1` anywhere in `src/` is
  `src/app/debug_adapter_host_v1.spl`, which presumably also fails for the same reason
  (out of scope for this lane — not investigated further).

`DebugWireV1`/`debug_wire_v1` never existed anywhere in `src/`'s history. This is a planned
wire-result type for the "central debug service v1" CLI surface that was referenced by a spec
and by the module under test, but whose actual definition was never written before the file
sweep landed.

### `sdb_command_contract_v1`
`src/app/cli_debug/commands.spl` is a 6-line re-export shim (`export use
app.cli_debug._DebugCommands.session_and_backend.*` /
`app.cli_debug._DebugCommands.command_dispatch.*`). Neither submodule under
`src/app/cli_debug/_DebugCommands/` defines `sdb_command_contract_v1`
(`grep -rn "sdb_command_contract" src/app/cli_debug/_DebugCommands/` → 0 hits). The spec file
`test/01_unit/app/cli_debug/debug_service_harmony_spec.spl` has exactly one commit in its
history — the same `e274cd33719` bulk sweep — and no commit has ever added a function of this
name anywhere in `src/` (`grep -rn "fn sdb_command_contract_v1" src/` → 0 hits at every commit
checked). This is a spec written against a planned "interactive debug CLI <-> DebugServiceV1
harmony" contract function that was never implemented.

## Outcome classification
Case (c) from the lane brief: **the module/function never existed** — these are specs written
against a planned surface, landed via a bulk single-commit file sweep (`e274cd33719`) without the
corresponding product code ever being written or verified compilable.

## Decision needed
For each spec, a maintainer must choose:
1. Implement the missing symbol (`debug_wire_v1`/`DebugWireV1` in
   `src/lib/common/debug/contracts_v1.spl`; `sdb_command_contract_v1` in
   `src/app/cli_debug/_DebugCommands/` or `commands.spl`) to match what the spec already asserts, or
2. Retire/rewrite the spec if the intended contract has been superseded or abandoned.

No product code or spec changes were made in this lane (out of scope per lane brief — import
lines were correct; the missing piece is product-side symbol definitions, not a stale import).
Both specs remain RED.
