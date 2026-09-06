# Stage 4 access CLI alias export and WM text boundary

## Status

Owner export and exact WM text-boundary repair PASS in focused and full-closure
verification. The full closure crossed this module before stopping later in the
T32 MCP session owner.

## Symptom

Exact x86 Phase 4 cycle 2 crossed the CLI utility owner repair, then HIR
lowering stopped in `src/app/play/wm_access_cli.spl` on unresolved type
`AccessOutputMode` despite its explicit import from
`common.ui.access_cli_grammar`.

## Evidence

- Log: `build/bootstrap-stage4-x86-phase4-llvm23/logs/x86_64-unknown-linux-gnu/stage4-native-build-cli-util-cycle2.log`
- Elapsed: 12m52.31s
- Peak RSS: 12,125,284 KiB
- Stub fallback: disabled
- LLVM provider: repository-managed 23.1.0-rc2 prefix

## Repair boundary

The physical grammar owner defines `AccessOperation` and `AccessOutputMode` as
text aliases but does not explicitly export them. Export those two aliases and
add a focused native import/signature contract. Do not duplicate aliases in the
WM adapter or widen type lookup.

`stage4_access_cli_type_alias_contract.spl` compiled and linked with stub
fallback disabled, then exited 30 with empty output. Evidence is retained under
`build/focused/stage4-access-cli-alias/`.

Two subsequent full-closure cycles proved that neither the access-hub re-export
nor a direct grammar import makes these text aliases available at the WM leaf's
Stage 4 type boundary. The accepted containment keeps the aliases inside their
grammar owner and uses their exact underlying `text` representation in the WM
adapter. This changes no accepted value or runtime behavior.

The strengthened contract imports and executes `wm_access_operation`, so the
real WM module and its hub/grammar topology are compiled. It linked 44 modules
and exited 30. Full Phase 4 cycle 3 then crossed the WM adapter and stopped
later in `app.mcp_t32.session_tools`, proving the original blocker is cleared.
