# VHDL process-facade system-test plan

## Scope

This plan covers `REQ-VHDL-SFFI-001`: public VHDL tool wrappers must use the
canonical pure-Simple captured-process facade and faithfully expose success,
exit code, stdout, and stderr. The executable owner is
`test/03_system/feature/usage/vhdl_spec.spl`; its manual mirror is
`doc/06_spec/03_system/feature/usage/vhdl_spec.md`.

Excluded: VHDL backend code-generation correctness, GHDL elaboration/run,
Yosys GHDL-plugin synthesis, FPGA implementation, and physical-board evidence.

## Requirement and acceptance matrix

| Requirement | Positive scenario | Edge scenario | Error scenario | Acceptance |
|---|---|---|---|---|
| `REQ-VHDL-SFFI-001` | qualified GHDL/Yosys discovery, exact file round-trip, valid GHDL analysis, code `0` | quiet success and noisy nonzero `VhdlToolResult` preserve exact streams | invalid VHDL returns failure, code `> 0`, nonempty captured diagnostic | 3 scenarios execute, 0 fail/drop; no blocked gate; docgen reports `0 stubs`; sspec-maintain has no blocker |

## Environment admission

- Runtime: admitted pure-Simple full CLI with `test`, `spipe-docgen`, and
  `sspec-maintain`. Rust seed, bootstrap-only CLI, and unadmitted artifacts are
  rejected as evidence.
- Host: `ghdl` and `yosys` on `PATH`.
- Gate: `SIMPLE_VHDL_TEST=1`.

The executable spec is fail-closed. With the gate absent it prints
`TEST_BLOCKED`, fails the expected `ready` value, and returns before process
execution. Missing runtime commands, tool binaries, verdicts, diagnostics, or
manual generation remain FAIL/`TEST_BLOCKED`, never a passing skip.

## Execution order

1. Confirm runtime admission and CLI capabilities without falling back.
2. Run the SSpec once:

   ```sh
   SIMPLE_VHDL_TEST=1 SIMPLE_TIMEOUT_SECONDS=3600 \
     <admitted-simple> test test/03_system/feature/usage/vhdl_spec.spl
   ```

3. Generate the mirror once:

   ```sh
   <admitted-simple> spipe-docgen \
     test/03_system/feature/usage/vhdl_spec.spl \
     --output doc/06_spec --no-index
   ```

4. Run maintainability once:

   ```sh
   <admitted-simple> sspec-maintain scan \
     test/03_system/feature/usage/vhdl_spec.spl
   ```

5. Review the mirror for all visible `step("...")` flows, complete folded
   executable source, requirement traceability, and explicit limitations.

## Current evidence status

`TEST_BLOCKED` on 2026-08-16: the only admitted pure-Simple runtime available
to this recovery lane is a bootstrap Stage2 CLI exposing `compile` and
`native-build`, not `test`, `spipe-docgen`, or `sspec-maintain`. The previously
passing admitted native process-facade probe proves the implementation but is
not substituted for these new system-test/documentization gates.

## Static and repository gates

Run once after final edits, both working and staged where supported:

```sh
sh scripts/check/check-vacuous-specs.shs --root test/03_system/feature/usage
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
sh scripts/audit/numbered-artifact-guard.shs --working
sh scripts/audit/numbered-artifact-guard.shs --staged
find doc/06_spec -name '*_spec.spl'
git diff --check
sh scripts/check/check-no-conflict-markers-push.shs <remote>..<commit>
sh scripts/check/check-no-conflict-tree-push.shs <remote>..<commit>
```

## Manual rendering policy

All three primary scenarios and their literal step flows stay visible. The
full Simple source is folded below them. There is no raster capture; meaningful
evidence is process exit/output plus the SSpec and docgen transcripts. The
manual must retain the `TEST_BLOCKED` provenance until qualified execution and
docgen actually pass.

## Risks

- A green edge-only scenario must not mask blocked tool-backed scenarios; the
  per-file verdict must show all declared examples executed with zero failures.
- GHDL may split diagnostics across stdout/stderr, so the error oracle checks
  their combined nonempty length while separately requiring nonzero status.
- `yosys_available()` is executable discovery, not plugin synthesis evidence.
- Shared `/tmp/ghdl_work` state must not be promoted to a durable artifact.
