# NVMe Firmware + Emulator Guide (TL;DR)

Two pure-Simple, **simulation-only** deliverables under `examples/09_embedded/simpleos_nvme_fw/`,
gated by `bin/simple run` (not `check`):

- **`fw/`** — layered NVMe SSD firmware: HIL/FTL/FIL + NVMe controller front end (admin,
  multi IO queue, round-robin, live thermal/SMART composite-temperature model (P7), and RAIN
  XOR-parity channel protection (P8) — both now WIRED into the live controller/FTL, not shelf)
  over an ONFI NAND device. Gates:
  `run fw/test_fw.spl` → `ALL FIRMWARE SELF-TESTS PASS` (526 asserts);
  `run fw/sim_main.spl` → `ALL END-TO-END CHECKS PASS`;
  `run fw/nvme_main.spl` → `ALL NVME CONTROLLER E2E CHECKS PASS` (also asserts the SMART
  composite temperature equals the live thermal model);
  `run fw/rain_ftl_check.spl` → `RAIN-FTL OK` (256 LBAs survive a whole-channel uncorrectable
  failure; gated in the system spec).
- **`emu/`** — host-interface ↔ device-interface emulator over a **settable memcpy seam on both
  sides**, ONFI NAND (2×2×2×2×8 = 128 pages), domain newtypes, Lean4 proofs. Gates:
  `run emu/nvme_emu_main.spl` → `EMU E2E PASS` (38 checks; steps 4/5 = fault-inject seam proof);
  4 per-module selftests (116 asserts); `lean emu/proofs/{Addr,Memcpy,Queue,Resource}.lean` exit 0.

Honest caveats: **newtypes are NOT enforced** on this binary (bug filed); the **Lean proofs are
standalone hand-transcribed algorithm models with no mechanical link to executed bytes**; the
Simple firmware was **NOT booted on rv32** — the rv32 LLVM native-build is currently broken in
this environment (exits 255, no diagnostic; the proven full-OS recipe also fails; the bootable
ELF is stale; boot NOT observed). See
`doc/08_tracking/bug/native_build_rv32_baremetal_silent_255_2026-06-30.md`.

P9 artifact: `fw_rv32/entry.spl` — a scalar/array-free re-expression of the RAIN reconstruct
(check-clean + host-verified, but build-environmentally-blocked on rv32 per the bug above).

Base-spec system evidence is now split from the boot blocker:
`test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl` runs the
host controller lifecycle plus `fw_rv32/base_spec_check.spl` for Identify,
queue lifecycle, Read, Write Zeroes, DSM Trim, Flush, Features, namespace guards,
logs, Format NVM, firmware command guards, and Abort/backpressure markers. The
rv32 ELF/QEMU proof still depends on the open native-build blocker.

<!-- sdn-diagram:id=nvme_fw_emu_tldr -->
```
  fw/   host SQ/CQ ─► [nvme_admin+qset+controller] ─► HIL ─► FTL ─► FIL ─► ONFI NAND device
  emu/  HOST ──host memcpy──► SharedMem ◄──dev memcpy── DEVICE ─► FTL ─► ONFI NandArray
            (NvmeEmu owns shared + ftl + nand + both DMA ports;  Lean4: Addr/Memcpy/Queue/Resource)
```

Full guide: `nvme_firmware_and_emulator_guide.md`.
