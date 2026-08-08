# Bug: rv64gc core has no RV64C (compressed) decode — real OpenSBI desyncs at insn ~5

- **ID:** rv64_core_no_c_extension_opensbi_stall
- **Date:** 2026-07-22
- **Status:** OPEN
- **Severity:** high (blocks booting any C-compiled RV64 firmware on soc_top_64)
- **Component:** `src/lib/hardware/rv64gc_rtl/core.spl`, `.../decode.spl` (RTL core datapath)

## Symptom
Booting the real OpenSBI v1.4 `fw_payload.bin` on `soc_top_64` (via the extended
`test/01_unit/lib/hardware/soc_rtl/opensbi_boot_probe.spl`, Case 3) never
produces UART output. The core executes the 32-bit `_fw_start` prologue
correctly, then, from ~instruction 5, `pc` wanders through misaligned code and
ends up looping in the trap-handler region (`_trap_handler` @ `0x8000_03f8`)
indefinitely. `mcause` stays 0 throughout — it is **not** a trap.

## Root cause (exact first divergence)
Instruction stream from reset (`pc=0x8000_0000`, boot ABI `a0=0`,
`a1=0x8800_0000` with `soc_virt.dtb`):

| pc | insn | kind | core delta | correct delta |
|----|------|------|-----------|---------------|
| `0x8000_0000` | `0x00050433 add s0,a0,zero` | 32-bit | +4 | +4 ✓ |
| `0x8000_0004` | `0x000584b3 add s1,a1,zero` | 32-bit | +4 | +4 ✓ |
| `0x8000_0008` | `0x00060933 add s2,a2,zero` | 32-bit | +4 | +4 ✓ |
| `0x8000_000c` | `0x53c000ef jal fw_boot_hart` | 32-bit | +1340 | +1340 ✓ |
| **`0x8000_0548`** | **`0x557d c.li a0,-1`** | **RVC (16-bit)** | **+4** | **+2** ✗ |

At `0x8000_0548` (`fw_boot_hart`, the first `jal` target) the core meets the
first **compressed** instruction `0x557d` (`c.li a0,-1`). The datapath:

- `core.spl` computes only `pc_plus4 = pc + 4` (~line 370); there is no `pc+2`
  path for 16-bit instructions.
- `decode.spl` decodes no compressed encodings (no `(insn & 3) != 3` branch, no
  RVC→32-bit expansion); it interprets the 32-bit word at `pc`
  (`0x8082_557d` = `c.li` ‖ `c.ret`) as one 32-bit instruction.

So `pc` advances to `0x8000_054c` instead of `0x8000_054a`, **skipping the
`c.ret` (`0x8082`)** and desyncing the fetch stream at every subsequent
compressed instruction. OpenSBI is compiled with the C extension (dense RVC), so
execution immediately degrades into misaligned garbage.

`misa` reports **RV64IMA`C`** (`misa_rv64imac()` in `csr.spl`), and
`csr_s.spl:206` even comments "IALIGN=16 with C extension" — the design *intends*
C support, but the datapath implements none. The existing M-mode stub gate
passes only because its payload is 100% 32-bit encodings.

## Impact
No C-compiled RV64 firmware (OpenSBI, Linux, any gcc `-march=…c` binary) can run
on `soc_top_64`. This is the single first blocker for a real firmware boot;
S-mode/PMP/DTB gaps are never reached (execution stalls at insn ~5).

## Fix
Implement RV64C in the core datapath:
1. Fetch a 16-bit half at `pc`; if `(half & 3) != 3` it is compressed.
2. Expand the 16-bit form to its 32-bit equivalent before `decode`/execute
   (standard RVC quadrants 0/1/2), or decode RVC directly.
3. Add a `pc+2` step for compressed instructions (IALIGN=16); keep `pc+4` for
   full instructions. Branch/jump targets already land on 2-byte boundaries.

## Predicted next divergence (after C lands)
`sbi_hart_pmp_configure` (`0x9_1be`) writes `pmpcfg0`/`pmpaddr0`
(`0x3A0`/`0x3B0`) — both **unknown** to `core64_machine_csr_known`, which
fail-closes to an illegal-insn trap. `menvcfg` (`0x30A`) and `mcounteren`
(`0x306`) are likewise unknown. Add these CSRs (even as WARL/no-op stubs) for
OpenSBI to progress past hart init toward console output.

## Evidence
`test/01_unit/lib/hardware/soc_rtl/opensbi_boot_probe.spl` Case 3 asserts this
divergence deterministically (`pc 0x8000_0548 → 0x8000_054c`, delta 4 not 2).
Reproduce: `bin/simple run test/01_unit/lib/hardware/soc_rtl/opensbi_boot_probe.spl`
(requires `sh scripts/os/build_opensbi_rv64_soc.shs` to have produced
`build/os/opensbi_rv64_soc/fw_payload.bin`).
