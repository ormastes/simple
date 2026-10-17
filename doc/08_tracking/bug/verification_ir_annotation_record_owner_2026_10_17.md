# Verification IR extraction annotation uses the wrong record owner

Date: 2026-10-17. Status: SOURCE-CONFIRMED; compilation/runtime qualification UNRUN. Bug database reconciliation pending.

Introduced by1c85a8541c9fde3a6a662a64121702be1edc4a66. In verification_ir.spl, VerificationIrModuleV1.functions is declared [VerificationIrFunction] (line595 at that commit), but canonical_text now annotates its extracted element as MirFunction (line619). The following statement reads symbol and semantic_hash from the verification record. MirFunction is the distinct executable MIR graph record; sharing a symbol field does not make their layouts/types interchangeable. The annotation cannot be accepted as a valid ANY-transport repair.

The same commit adds four MirBlock annotations across verification_call_identity.spl and verification_ir.spl while their explicit terminal imports name only MirFunction and MirModule. Add MirBlock to the existing compiler.mir.mir_instruction_graph import in both files; do not rely on incidental cross-module type visibility.

Correction: declare the canonical-text element as its actual local VerificationIrFunction type, and add the two missing terminal imports. Canonical hash framing, iteration order, method algorithms, owner identities and all validations are otherwise unchanged. VerificationIrFunction is declared in the same file, so no new visibility/export is needed. No runtime ABI cast, manufactured record, permissive fallback or verification bypass is introduced.

Source evidence: the original18-file remote sweep normalizes exactly to its parent after removing the intended annotations/import addition and folding the one typed call-argument extraction. That inverse proves there are no other algorithm edits; it does not establish annotation correctness or runtime safety. Independent declaration review found this concrete wrong type and missing imports. The remote commit's stated HIR-check result was not independently reproduced.

Validation: source review and focused diff/guard/layout checks only. Required compiler/lib/MCP/LSP and native/SPipe checks remain UNRUN because a qualified full self-hosted compiler is unavailable in this session. Do not claim native success, compiler admission, Phase3 completion, deployment or release. This minimal correction must remain draft until applicable qualification is established.
