# Stage 4 access CLI type alias export

## Status

Owner export and real import-topology repair focused PASS. Exact Phase 4
verification requires a fresh bounded session.

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

The final bounded Phase 4 cycle reproduced unresolved `AccessOutputMode` in the
WM adapter. The initial focused contract imported only the grammar owner and
therefore missed the real module's simultaneous access-hub import. The repaired
topology imports semantic aliases through `common.ui.access` and grammar
constants directly; the strengthened contract mirrors that split. No fourth
full Phase 4 cycle is permitted in this continuation.

The strengthened topology contract compiled and linked, then exited 30 with
empty output. Evidence: `build/focused/stage4-access-cli-alias/` files ending
in `-topology`.
