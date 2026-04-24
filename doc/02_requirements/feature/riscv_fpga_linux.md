# RISC-V FPGA Linux Feature Requirements

Superseded as the canonical Linux-capable hardware/program scope by `rv64_linux_rtl_pipeline`.
This file remains historical context for the earlier mixed-lane orchestration and helper-proof milestone only.

Historical requirement interpretation:

- REQ-RFL-001..002 remain the board-profile baseline for prepare-only generation and hardware-boot gating.
- REQ-RFL-003..007 now describe orchestration history, not current Linux truth. Current repo truth is RV64-first; RV32 remains compiler-parity only and default output no longer claims a first-class RV32 Linux CPU/RTL lane.
- REQ-RFL-008..011 are complete for the bounded helper-proof milestone. The implemented helper set is `decode_writeback`, `decode_branch_immediate`, `decode_store_immediate`, `decode_i_immediate`, `decode_upper_immediate`, `decode_execute_control`, and `decode_jump_immediate`, with exact MIR/VHDL/source-map assertions.
- No requirement in this historical file should be read as a claim that the repo already has a full Linux-capable generated CPU or SoC. CSR, privilege, MMU runtime behavior, interrupts, traps, and Linux boot proof remain outside this artifact.
