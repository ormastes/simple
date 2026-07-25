# NVMe Firmware + Emulator Guide (TL;DR)

Two main pure-Simple host deliverables plus one rv32 direct-smoke image live under
`examples/09_embedded/simpleos_nvme_fw/`:

- **`fw/`** — layered NVMe SSD firmware: HIL/FTL/FIL + NVMe controller front end (admin,
  multi IO queue, round-robin, live thermal/SMART composite-temperature model (P7), and RAIN
  XOR-parity channel protection (P8) — both now WIRED into the live controller/FTL, not shelf)
  over an ONFI NAND device. Gates:
  `run fw/test_fw.spl` -> `ALL FIRMWARE SELF-TESTS PASS` (1174 asserts);
  `run fw/sim_main.spl` → `ALL END-TO-END CHECKS PASS`;
  `run fw/nvme_main.spl` → `ALL NVME CONTROLLER E2E CHECKS PASS` (invalid namespace rejection
  plus SMART composite temperature from the live thermal model);
  `run fw/rain_ftl_check.spl` → `RAIN-FTL OK` (256 LBAs survive a whole-channel uncorrectable
  failure; gated in the system spec).
- **`emu/`** — host-interface ↔ device-interface emulator over a **settable memcpy seam on both
  sides**, ONFI NAND (2×2×2×2×8 = 128 pages), domain newtypes, Lean4 proofs. Gates:
  `run emu/nvme_emu_main.spl` → `EMU E2E PASS` (38 checks; steps 4/5 = fault-inject seam proof);
  4 per-module selftests (116 asserts); `lean emu/proofs/{Addr,Memcpy,Queue,Resource}.lean` exit 0.

Honest caveats: **newtypes are NOT enforced** on this binary (bug filed); the **Lean proofs are
standalone hand-transcribed algorithm models with no mechanical link to executed bytes**; the
rv32 direct-smoke path needs `build/nvme_fw_rv32.elf` before it can prove a QEMU boot, and the
full no-alloc firmware port remains open.

P9 artifacts: `fw_rv32/entry.spl` is the scalar/array-free reference, and default
`fw_rv32/build.shs` is the fast direct rv32 smoke ELF recipe; QEMU boot evidence exists only
after `build/nvme_fw_rv32.elf` is produced and prints `ALL RV32 NVME FW CHECKS PASS` /
`RESULT: PASS`.

<!-- sdn-diagram:id=nvme_fw_emu_tldr -->
```
  fw/   host SQ/CQ ─► [nvme_admin+qset+controller] ─► HIL ─► FTL ─► FIL ─► ONFI NAND device
  emu/  HOST ──host memcpy──► SharedMem ◄──dev memcpy── DEVICE ─► FTL ─► ONFI NandArray
            (NvmeEmu owns shared + ftl + nand + both DMA ports;  Lean4: Addr/Memcpy/Queue/Resource)
```

Full guide: `nvme_firmware_and_emulator_guide.md`.
