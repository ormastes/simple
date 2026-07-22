# soc_rtl bootrom is RV32-encoded — RV64 boot-to-DRAM handoff misjumps

**Filed:** 2026-07-22 (lane W2-D bonus finding)
**Status:** OPEN
**Severity:** medium (RV64 SoC boot path; workaround exists)

`src/lib/hardware/soc_rtl/bootrom.spl` encodes the reset-vector trampoline for
RV32: `lui t0, 0x80000; jalr t0`. On RV64, `lui` sign-extends bit 31, so t0 =
`0xFFFF_FFFF_8000_0000`, not `0x8000_0000` — the jump to DRAM base lands at a
non-canonical address instead of the kernel load address.

**Fix direction:** RV64 bootrom needs a sequence that produces a zero-extended
`0x8000_0000` (e.g. `lui` + `srli`/`slli` pair, or `auipc`-relative), or a
64-bit-aware bootrom variant selected by XLEN.

**Workaround in tree:** soc_top_64 specs/probe set `soc.core.pc = 0x8000_0000`
directly instead of booting through the ROM (noted in the spec comments).

**Evidence:** W2-D probe case3 executes the real bootrom `lui` at 0x1000 on the
wired RV64 datapath and observes the sign-extended value in the register
(sp == sext(0x80100000) for the stack-setup lui at 0x1004).
