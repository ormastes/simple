# Scalar regression cannot qualify selected compiler bodies

Status: HOLD. Source-only diagnosis; no repair or fourth execution is admitted.

The final exported-storage candidate diagnostic exited 1 with a closed Windows
Job. It observed all 18 required source owners without an outside read or changed
source pin. Nevertheless, three named tests failed and the flat-storage test
aborted before the ELF-byte criterion. There is no five-case PASS.

Evidence packet: `build/native_probe/exported-scalar-storage-20261013-astra/`.
The candidate is `storage-candidate-v6/CANDIDATE.patch`, SHA256
`c926a6a6af5480002fc394614e52d12135a55e11877f1b77fd9c2df053d92ebb`.
The final receipt is `candidate-cycle3/receipt.env`, SHA256
`2eb810d0d6e2d4d874f037d333faac395d0087b6169499d88dfbd19a1bc0d020`.
The authorized Phase 1 diagnostic producer is SHA256
`d95807daf8725254e6737f12b0a81965ac5ae0a9236b19eedac94940bd9867f1`.

Two named failures reported that `SymbolTable` lacks `admitted_function_abis`.
A bounded search of the admitted candidate compiler tree found no reference
to that field. The current shared compiler tree does reference it, including
`20.hir/hir_types.spl:305` and `50.mir/_MirLowering/module_lowering.spl:1478`.
This difference is a diagnostic lead, not proof that shared source was read.

Another failure reported that `HirLowering` lacks
`registering_field_dependency`. The admitted candidate declares that field in
`20.hir/hir_lowering/types.spl:433` and initializes it at line 753. Its flat
path subsequently reported an exported-storage index out of range.

Source-read observations do not identify the selected function body, class
schema, constructor, or embedded/cache provenance. The present evidence cannot
distinguish an incorrect dispatch route from another schema or producer defect.
Adding fields or altering storage indices solely to silence these failures
would therefore be an unqualified workaround.

Required repair evidence: bind selected function and constructor identities,
their source or embedded-artifact digests, class schema, and cache generation;
then exercise the actual owner through an authenticated producer. Preserve
negative controls for colliding module/class names and stale generations.
Keep authored visibility private and retain the invalid-array guard. The
current feature's three-cycle diagnostic limit is exhausted; retain its result
and use a genuinely repaired producer before any separately admitted follow-up.

Related retained evidence:
`phase4-linker-gen-sdn-api-audit-20261013-astra/ROOT_COALESCE_DISPATCH_AUDIT.md`
already distinguishes reading a patched owner from selecting its function body.
Neither report establishes a rebuilt compiler, native ELF link, plugin transport
support, memory safety, or a compilation performance improvement.
