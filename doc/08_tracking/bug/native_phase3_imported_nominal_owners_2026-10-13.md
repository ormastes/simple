# Native Phase3 imported nominal owners

Observed source ffad3e66284a4dd13fcf2415e086ca4cd5295803 with pure-Simple producer SHA256 3e7aca25146e2362aef9362c3ad83fc3a74b0799652492b5716dd162bfe46440 (source7c91). The diagnostic finished 1319 visits, but its ledger contained1305 successful lowerings and14 failed modules; no object generation or Phase3 link occurred. Progress rows incorrectly reported visited units as succeeded. Failed receipts and1305 HIR cache stores remain preserved outside the source tree.

## Corrections

- Import the existing enum_payload_named_alias_equal helper at its calling source. The sibling helper was called without being named in the import list.
- Change the declaring archive schema owner to brace-import MonoArchiveNominalDeclV2 explicitly. The bare dotted spelling produced an empty named-item span; enum payload dependency materialization only inspected named items. Keep NominalDeclarationV2 and its full payload.
- Explicitly import canonical hidden signature/field dependencies in the remaining failed consumers: MirType/MirSignature/LocalId from compiler.mir.mir_types, SymbolId from compiler.hir.hir_types, ImplBlock from compiler.traits.trait_impl. Do not use the distinct trait_method_resolution.ImplBlock class. These imports do not change declarations, fields, variants, configured library families, or ownership guards.

## Remaining compiler defects

The consumer imports are compatibility workarounds for a transitive declaration materialization defect: field/signature type identifiers must resolve in the declaring owner's scope, with qualified identity and ambiguity refusal. Consumers should not need to import a hidden dependency merely to materialize another owner's declaration. Preserve compact bare import syntax; fix its named-item dependency extraction instead of silently removing the language form. Record both as pending compiler repairs.

## Verification boundary

Patch prepared from actual independent failed-module diagnostics. No new native object, executable, or full Phase3 PASS is claimed by this document. Validate failed modules individually with the exact producer/runtime and actual ELF relocatable artifacts, then compile/run Phase3 before landing. Ordinary memory/performance gates remain deferred only for the explicitly authorized diagnostic attempt; full admission is unproven. Full core/MCP/LSP verification remains required for final qualification.

## Isolated manual object findings

The first enum-caller mini passed its own prior missing-helper boundary, but its narrower381-module closure exposed a hidden MirType dependency in optimizer_manifest. The957-module archive mini still reports NominalDeclV2 in the consumer after fixing the owner's brace import. This confirms that named dependency extraction alone does not repair old-producer transitive field materialization. Explicit canonical imports were additionally added to those two consumers. Retain failed receipts; no successful object/Phase3 evidence is inferred from partial lowering or progress counters.
