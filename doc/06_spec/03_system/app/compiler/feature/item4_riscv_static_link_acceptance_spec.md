# RV64 static ELF acceptance

Authority: `test/03_system/app/compiler/feature/item4_riscv_static_link_acceptance_spec.spl`.
Requirements: ITEM4-REQ-003, 004, 006, 007. Status: authored manual; Simple execution and canonical
SPipe regeneration are **UNRUN**. This is not generated PASS evidence.

1. Link real RV64 objects directly and through archive extraction; inspect the
   ELF machine, ABI flags, entry and independent instruction/data byte oracles.
2. Resolve nonadjacent PC-relative HI/LO pairs, GOT references, call/branch
   instructions and ordered arithmetic relocations.
3. Reject malformed pair labels/addends, missing high relocations, incompatible
   floating ABIs, branch overflow and patches outside their input section.
4. Resolve fixed-width SET/SUB ULEB pairs; preserve allocated field width and
   reject malformed ordering, negative/oversized values or truncated fields.
5. Normalize validated ALIGN NOP padding, updating symbol extents and relocation
   places while preserving explicit addends. Compare real LLVM fixture oracles.

The admitted image is little-endian RV64 static ET_EXEC. RV32 output, dynamic
linking/TLS and actual RV64 host execution are not established by this manual.

