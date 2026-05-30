# GHDL RV32 Mailbox Lane Completion Report

**Date:** 2026-04-04  
**Status:** Implemented (host-aware)

## Summary

The `ghdl_rv32_mailbox` lane is now promoted from `in_progress` to `host_aware`. This lane provides a debugger-independent GHDL simulation proof row that communicates via MMIO memory-mapped mailbox registers instead of ARM semihosting trap instructions. The mailbox protocol operates at base address `0x80FF0000` with three commands (PUTC, EXIT, RESULT) and collects results via a ram_sentinel at `0x80008000`.

## Architecture

The mailbox lane is intentionally distinct from the semihost lane:

| Property | Semihost Lane | Mailbox Lane |
|----------|--------------|--------------|
| Communication | ARM semihosting trap sequence | MMIO register writes |
| CPU dependency | Requires semihost-aware CPU trap detection | Works with any RV32I core (standard store instructions) |
| GDB required | Yes (GDB-MI client) | No (direct simulation execution) |
| Result channel | semihost_text | ram_sentinel |
| Testbench | tb_semihost.vhd | tb_mailbox.vhd |

### MMIO Protocol

Base address: `0x80FF0000`

| Offset | Register | Direction | Purpose |
|--------|----------|-----------|---------|
| +0x00 | CMD | Target→Host | Command code (PUTC=0x01, EXIT=0x02, RESULT=0x03) |
| +0x04 | ARG0 | Target→Host | First argument |
| +0x08 | ARG1 | Target→Host | Second argument |
| +0x0C | STATUS | Host→Target | Response status |
| +0x10 | RESULT | Host→Target | Result value |
| +0x14 | SEQ_ID | Target→Host | Sequence counter |
| +0x18 | TRIGGER | Target→Host | Write 0xDEAD to fire command |

### Key Files

| File | Purpose |
|------|---------|
| `doc/04_architecture/ghdl_rv32_mailbox_protocol.md` | Protocol specification |
| `examples/09_embedded/fpga_riscv/rtl/rv32i_pkg.vhd` | VHDL constants (mailbox addresses, commands) |
| `examples/09_embedded/fpga_riscv/rtl/tb_mailbox.vhd` | VHDL testbench with MMIO decode |
| `examples/09_embedded/fpga_riscv/sw/mailbox.h` | Target-side C header (inline MMIO functions) |
| `examples/09_embedded/fpga_riscv/sw/hello_riscv32_mailbox.c` | Bounded test program |
| `src/lib/nogc_async_mut_noalloc/baremetal/ghdl_mailbox_runner.shs` | Runner script (ELF→simulation pipeline) |
| `src/lib/nogc_sync_mut/debug/remote/exec/adapter_ghdl_rv32.spl` | GhdlRv32MailboxAdapter class |
| `src/lib/nogc_sync_mut/debug/remote/exec/capability_report.spl` | probe_ghdl_mailbox() |
| `src/lib/nogc_sync_mut/debug/remote/exec/lane_registry.spl` | Lane promoted to host_aware |
| `test/feature/baremetal/ghdl_riscv32_mailbox_spec.spl` | Authoritative proof spec |

## Tests

| Spec File | Tests | Scope |
|-----------|-------|-------|
| `test/feature/baremetal/ghdl_riscv32_mailbox_spec.spl` | 9 | Smoke, hello world, negative cases, protocol contract |

## Explicit Decisions

### Completed

- Mailbox MMIO protocol defined and documented
- VHDL testbench with MMIO address decode (no semihost dependency)
- Target-side C runtime (inline MMIO functions)
- Runner script (ghdl_mailbox_runner.shs)
- Simple adapter (GhdlRv32MailboxAdapter — no GDB-MI)
- Capability probe (probe_ghdl_mailbox)
- Lane registry promotion to host_aware
- Proof spec with smoke, positive, negative, and contract tests

### Deferred

| Item | Reason | Tracking |
|------|--------|----------|
| Full remote interpreter protocol | First milestone is bounded (3 commands) | Future expansion |
| Multi-command sequences | Single-command exchange sufficient for proof | Future enhancement |
| Bidirectional status handshake | Target-to-host is sufficient for proof | Protocol v2 |

## Known Limitations

- The mailbox lane requires the same host toolchain as semihost (ghdl, clang, ld.lld, llvm-objcopy)
- The ELF binary must be pre-built — the lane runner does not compile from source
- Timeout detection depends on GHDL simulation cycle count, not wall-clock time

## References

- Protocol: `doc/04_architecture/ghdl_rv32_mailbox_protocol.md`
- Lane matrix: `doc/08_tracking/lane_matrix.md`
- Semihost lane report: `doc/09_report/remote_baremetal_completion_2026-04-04.md`
- Closure plan: `doc/03_plan/distinctive_features_completion_closure_plan_2026-04-04.md`
