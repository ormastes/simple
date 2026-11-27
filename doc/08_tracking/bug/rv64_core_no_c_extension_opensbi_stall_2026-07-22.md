# Bug: rv64gc core has no RV64C (compressed) decode — real OpenSBI desyncs at insn ~5

- **ID:** rv64_core_no_c_extension_opensbi_stall
- **Date:** 2026-07-22
- **Status:** RESOLVED 2026-11-25 — RV64C expansion + pc+2 landed; verified by direct expansion probe on the exact divergent instruction (full OpenSBI boot not re-run; riscv toolchain absent on this host)
- **Severity:** high (blocks booting any C-compiled RV64 firmware on soc_top_64)
- **Component:** `src/lib/hardware/rv64gc_rtl/core.spl`, `.../decode.spl` (RTL core datapath)

## Resolution 2026-11-25 (p2w4-ag lane, release/1.0.0 @ 63e791180d3)

The Fix section's three steps are all implemented in the current tree:

1. **RVC detect + expand before decode:** `src/lib/hardware/rv64gc_rtl/decode.spl`
   implements `rvc_expand(iword) -> RvcExpansion` (line 376) with canonical
   quadrant-0/1/2 expanders (lines 220/251/328), gcc-objdump-cross-checked
   encodings, and fail-closed `legal=false` for reserved patterns — exactly
   the doc's `c.li 557d -> fff00513` case is in its verified table.
2. **pc+2 step:** `core.spl:75-87` computes `pc_incr = 2 if exp.compressed
   else 4` and decodes the expanded 32-bit form; `csr.spl:220-221` keeps
   2-byte-aligned trap/mret pcs (no more `& ~3`).
3. **Predicted next divergence (PMP/menvcfg CSRs):** also landed —
   `csr.spl:362-392` adds extended CSR storage for `pmpcfg0-3` (0x3A0-0x3A3),
   `pmpaddr0-15` (0x3B0-0x3BF), `menvcfg` (0x30A), `mcounteren` (0x306),
   `scounteren` (0x106); `core_helpers.spl:200` recognizes the PMP range.

**Verification:** `bin/simple.exe test` is env-blocked repo-wide at HEAD
(pinned seed rejects `@representation_boundary`), so the probe was run in
`run` mode against the public expander
(`hardware.rv64gc.core.rv64_compressed`):

```text
decompress_rvc(0x557d)  -> 0xFFF00513  (c.li a0,-1 = addi a0,x0,-1)  compressed=true
decompress_rvc(0x0000)  -> 0           (reserved c.addi4spn nzuimm=0, fail-closed)
RVC PROBE PASS
```

The full OpenSBI Case-3 boot probe was **not** re-run: it needs
`build/os/opensbi_rv64_soc/fw_payload.bin` from
`scripts/os/build_opensbi_rv64_soc.shs`, and no riscv cross toolchain is
present on this host. The exact instruction-level divergence recorded above
(the bug's own root cause) is demonstrably fixed; unit coverage exists at
`test/01_unit/hardware/rv64gc/rv64_compressed_spec.spl` and
`rv64_pmp_csr_spec.spl` for the next toolchain-equipped run.

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
