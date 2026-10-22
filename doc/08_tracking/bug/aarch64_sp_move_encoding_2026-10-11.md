# AArch64 stack frame moves encode the zero register

REQ-AARCH64-SP-MOVE-001: A64_OP_MOV operands naming AARCH64_SP must copy the
stack pointer, while ordinary register moves keep their ORR register alias.

Status: source repaired; four exact-byte cached Stage 1 diagnostics pass.
Admitted self-hosted runtime and required compiler/core/MCP/LSP gates remain
pending. No compiler was rebuilt and no retained cache was invalidated.

At release c4cd4530c1d4e61d74ce669d54b9e26c0d625a44, encode_aarch64.spl emits
ORR shifted-register for every A64_OP_MOV. In that form, register 31 is XZR.
The production selector emits MOV x29,sp for frame setup and MOV sp,x29 for
frame restore; the old bytes therefore clear x29 and discard the sp restore.
The same issue affects copying sp for stack allocations.

SP-involving MOV now emits ADD-immediate #0 (0x91000000 with Rn and Rd).
General register MOV keeps its ORR encoding. Current caller review found SP
uses in frame setup, restore, and allocation; the physical allocator does not
allocate register 31 to ordinary virtual registers.

Architecture references: [Arm A64 compiler overview](https://developer.arm.com/community/arm-community-blogs/b/architectures-and-processors-blog/posts/the-a64-isa-and-compilers)
explains the context-dependent SP/zero-register identity; [Arm porting guide](https://developer.arm.com/-/media/Files/pdf/graphics-and-multimedia/Porting%20to%20ARM%2064-bit.pdf)
identifies ADD-immediate as accepting SP in the destination and first operand.

Evidence: build/phase1-aarch64-sp-move-20261011 contains source-inline copies
of the actual release mach_inst, operand_utils, encode_common and encoder
owners plus the executable regression body. Only module use/export directives
were omitted for concatenation. These diagnostics do not prove module import
resolution, native execution, or release admission.

- Baseline: four executed, one passed, three failed.
- Repaired: four executed, four passed, zero failed/skipped/dropped; child exit
  zero; final_job_active=0; peak RSS 46,504 KiB.
- Cached Stage 1 producer SHA256:
  15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb.
- Repaired encoder SHA256:
  b7e4874d6f20a8489d244f052e49bb29fc273d4972e250f7ce6c166313d0cf99.

Independent parent review found no P0/P1 issue and ran an llvm-mc 23 AArch64
assembler oracle, without replaying the Simple diagnostics. Its bytes were
MOV x29,sp = fd 03 00 91; MOV sp,x29 = bf 03 00 91;
MOV sp,sp = ff 03 00 91; MOV x0,x1 = e0 03 01 aa.
These independently confirm the ADD-immediate SP alias and ordinary ORR alias.
Assembler evidence does not replace admitted runtime or native execution gates.

The historical global_addr_aarch64_riscv64_contract invocation remained failed:
its wrong memory-operand refusal was a distinct cause. The separately retained
frame-pair operand repair addresses that cause at source level; neither repair
claims the original full invocation passed. AVX2's retained instruction-count oracle also
needs independent current-source review before attributing it to codegen.

Regression: test/01_unit/compiler/backend/native/aarch64_sp_move_encoding_spec.spl.
Manual: doc/06_spec/01_unit/compiler/backend/native/aarch64_sp_move_encoding_spec.md.
No instruction IR, encoded format, architecture boundary, or UI changes.

## Current merge qualification

The observations above belong to their pinned historical producers and source
owners. The current release_phase3 merge retains the source repair, but its
admitted compiler/core/MCP/LSP and full Phase 3 qualification remain pending.
No historical diagnostic or experimental native fixture is a current merge PASS.
