# Native ISel specs lost fixture definitions in the release transplant

Status: fixture source repaired; focused Stage 1 diagnostics pass. Admitted
self-hosted import closure, native execution and compiler/core/MCP/LSP gates
remain outstanding. No compiler rebuild or cache invalidation occurred.

The retained Phase 1 isel_riscv64_spec recorded 42 executed, six passed and
36 failed. Most failures named missing helpers such as build_memory_module,
prologue_block and count_opcode. Current release 4a3644f512135f4a07069fd299536203ac361f06
still lacked these bodies after transplant commit 88aac2ffe28. Pre-transplant
f2378f0b4c8 contains the original implementations.

Restore those exact bodies into two test fixture modules (661 and 454 lines),
with explicit imports and the original machine-opcode imports in the executable
spec. No original scenario is dropped. The helper module declarations are
public for imports; their bodies are unchanged. The observer module retains its
own find_opcode implementation for internal calls; that name is not imported
over the spec's existing local helper.

The old Abort oracle requested a NOP. Actual production rv_isel_terminator's
Abort arm explicitly emits EBREAK so control cannot fall into a following block.
The strengthened oracle now requires one operand-free EBREAK and zero NOPs.

X86 isel_x86_64_spec's two Abort scenarios likewise lacked build_abort_module.
Restore its 49 lines from pre-transplant ae55a746719, preserving both INT3 and
non-NOP assertions. Other X86 scenario bodies and product source are unchanged.

Evidence under build/phase1-backend-fixtures-20261011:

- RV64 baseline current-owner diagnostic reproduced 36 failures and six passes.
  Intended historical-green filtering initially missed ANSI coloring; repaired
  diagnostics strip ANSI codes and exclude those six already-green scenarios.
- Fixture repair: selected 36 formerly failed cases; 35 passed, one failed only
  because the Abort oracle still expected NOP. Peak RSS 301,640 KiB.
- Final RV64 cycle: only the corrected Abort scenario ran and passed; the 35
  repaired-green cases were not replayed. Peak RSS 300,152 KiB. Three cycles used.
- X86 initial selected diagnostic had an empty-describe grouping parse failure.
  Corrected ephemeral grouping preserved both selected scenario bodies and
  passed two of two, zero skipped/dropped. Peak RSS 145,172 KiB. Two cycles used.
- Successful final receipts record child exit zero and final_job_active=0.

Diagnostics inline actual current native selector text plus the restored test
bodies; the supporting compiler/stdlib import closure remains historical.
They do not prove current-source import resolution, admitted runtime behavior,
native execution or a whole-spec PASS. The cached bootstrap producer SHA256 is
15102d32226b3fbead63d3c63e33e99a6f0e9ffcddea06080fb65872445cbafb.

The historical RV32 ISel fixture family is already restored by bf2bb4a0f0c,
and RV32/RV64 encoding fixtures by dbc86d6a5cb. Those source restorations do
not upgrade the historical outcomes without current qualification.

The default bin/release runtime is absent on this host. The cached pure
candidate b580919372e209ea2a10e6d8e919b0f90c5dc3100e76f958f584c5db0ace4778
remains diagnostic, with no six-product admission. Its exhausted hello scope
was not restarted. Required qualified gates remain explicit PR blockers.
