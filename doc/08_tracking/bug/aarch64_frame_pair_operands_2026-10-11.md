# AArch64 frame pairs reject the selector's operand form

REQ-AARCH64-FRAME-PAIR-001: Encode the selector's preindexed STP frame save and
postindexed LDP restore with writeback, preserving offset pair instructions.

Status: source repaired; four focused current-owner Stage 1 diagnostics pass;
admitted runtime, native execution and compiler/core/MCP/LSP gates pending.

Current release 571d6cefe3371e6153363d0a5d72ce9adebdfade emits frame STP/LDP
with four operands: two registers, a physical base register, and an immediate.
The encoder instead assumes three operands with a Mem base/offset operand.
That mismatch produces the retained global_addr_aarch64_riscv64_contract_spec
refusal: E-BACKEND-OPERAND-get_mem_base_id, expected Mem, got Reg.

The four-operand STP form now uses preindex writeback (0xA9800000); four-operand
LDP uses postindex writeback (0xA8C00000). Three-operand Mem forms retain their
offset encodings (0xA9000000 and 0xA9400000). The selector and allocator remain
compatible, and the operand accessors continue rejecting wrong operand kinds.

Focused current-release source-inline baseline reproduced both frame refusals
and passed both ordinary offset controls: two passed, two failed. The repaired
owner passed all four exact-byte scenarios, zero skipped/dropped; child exit
zero; final_job_active=0; peak RSS 48,468 KiB. Source owners were mach_inst,
operand_utils, encode_common and encode_aarch64, concatenated with only module
use/export directives removed. The executable regression body was unchanged.

Evidence: build/phase1-aarch64-frame-pair-20261011/{baseline,repaired}. Source
inline diagnostics do not prove current-source import closure, native execution,
or release admission. Cached Stage 1 producer SHA256:
15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb.
Two bounded cycles were used; no compiler rebuild or cache invalidation occurred.

Independent parent review found no P0/P1 issue in the selector/encoder pairing.
A separate pinned llvm-mc 23 AArch64 assembler oracle emitted fd 7b bf a9 for
the preindexed STP, fd 7b c1 a8 for postindexed LDP, fd 7b 00 a9 for offset STP,
and fd 7b 40 a9 for offset LDP. All four match the regression expectations.
This oracle was separate from the passing Simple diagnostic and does not
replace admitted runtime/native/compiler qualification gates.

The retained global_addr spec also has an independent source-text ELF layout
failure. No full invocation PASS is claimed. The SP MOV repair in PR #2990 is
also required for correct frame setup/restore; it is independent of this panic.

Regression: test/01_unit/compiler/backend/native/aarch64_frame_pair_encoding_spec.spl.
Manual: doc/06_spec/01_unit/compiler/backend/native/aarch64_frame_pair_encoding_spec.md.
No architecture boundary, encoded format, or UI change is introduced.

## Current merge qualification

The observations above belong to their pinned historical producers and source
owners. The current release_phase3 merge retains the source repair, but its
admitted compiler/core/MCP/LSP and full Phase 3 qualification remain pending.
No historical diagnostic or experimental native fixture is a current merge PASS.
