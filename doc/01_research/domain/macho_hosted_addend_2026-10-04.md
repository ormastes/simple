# ARM64 Mach-O ADDEND domain evidence

Primary sources searched 2026-10-04. No external linker execution is claimed by
this research; actual fixture provenance belongs to the acceptance lane.

- [LLVM RuntimeDyldMachOAArch64](https://llvm.org/doxygen/RuntimeDyldMachOAArch64_8h_source.html),
  lines 286–324, validates nonexternal/non-PC-relative prefix fields and length
  2, sign-extends the 24-bit `r_symbolnum`, and consumes the following relocation.
  Its assertion disallows simultaneous nonzero explicit and embedded addends.
  A zero explicit addend does not invalidate an otherwise valid embedded addend.
- [LLVM LLD relocation handling review D95121](https://reviews.llvm.org/D95121)
  describes ADDEND followed by BRANCH26 or PAGE21/PAGEOFF12 and sign extension.
  This supports preserving branch pairs already accepted by the Simple static
  engine, rather than narrowing them to page instructions.
- [LLVM MachO.h](https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/BinaryFormat/MachO.h)
  names relocation 10, but its comment mentions only PAGE21/PAGEOFF12. That
  comment is narrower than the assembler/linker implementation; it is not used
  to reject the existing BRANCH26 contract.

The signed payload domain is -8388608 through 8388607. The decoder validates
pair structure; the existing patch engine continues checking instruction
encoding, alignment, displacement range and load/store scale. Rejecting a
nonzero addend on an imported branch is the current Simple stub-routing policy,
not a claim that the Mach-O ABI globally prohibits such expressions.

Keep explicit scope boundaries: no ADDEND+GOT/TLV expansion, authenticated
pointer support, dynamic weak semantics or native Darwin readiness follows from
this repair. Real ARM64 object bytes plus independently decoded final
instructions must test the implementation; compile success alone is insufficient.
