# soc_rtl bootrom is RV32-encoded — RV64 boot-to-DRAM handoff misjumps

**Filed:** 2026-07-22 (lane W2-D bonus finding)
**Status:** FIXED (2026-07-22) — `bootrom_read64` landed and `soc_top_64`
fetch wired to it (`c95684a1862`); in-tree probe: full reset-vector→DRAM
handoff, pc lands 0x80000000, sp/a1/t0 zero-extended, specs updated.
**Severity:** was medium (RV64 SoC boot path)

`src/lib/hardware/soc_rtl/bootrom.spl` encodes the reset-vector trampoline for
RV32: `lui t0, 0x80000; jalr t0`. On RV64, `lui` sign-extends bit 31, so t0 =
`0xFFFF_FFFF_8000_0000`, not `0x8000_0000` — the jump to DRAM base lands at a
non-canonical address instead of the kernel load address.

**Fix (partial, 2026-07-22):** `bootrom_read64()` added to
`src/lib/hardware/soc_rtl/bootrom.spl` — 11-insn RV64 sequence zero-extending
each LUI with a slli/srli-by-32 pair (sp/a1/t0). Encodings executed on the
real core64 datapath: probe asserts sp=0x80100000, a1=0x88000000,
t0=0x80000000 (all zero-extended) and jalr lands at 0x80000000 — 5/5 PASS
(`test/01_unit/lib/hardware/soc_rtl/boot64_probe.spl`).
**Remaining:** wire `soc_top_64` fetch to `bootrom_read64` (deferred to avoid
colliding with the in-flight MMIO lane that owns soc_top_64.spl), then remove
the direct-pc workaround from the specs.

**Workaround in tree:** soc_top_64 specs/probe set `soc.core.pc = 0x8000_0000`
directly instead of booting through the ROM (noted in the spec comments).

**Evidence:** W2-D probe case3 executes the real bootrom `lui` at 0x1000 on the
wired RV64 datapath and observes the sign-extended value in the register
(sp == sext(0x80100000) for the stack-setup lui at 0x1004).
