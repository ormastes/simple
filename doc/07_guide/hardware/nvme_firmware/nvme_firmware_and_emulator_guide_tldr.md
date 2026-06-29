# NVMe Firmware + Emulator Guide (TL;DR)

Two pure-Simple, **simulation-only** deliverables under `examples/09_embedded/simpleos_nvme_fw/`,
gated by `bin/simple run` (not `check`):

- **`fw/`** — layered NVMe SSD firmware: HIL/FTL/FIL + NVMe controller front end (admin,
  multi IO queue, round-robin) over an ONFI NAND device. Gates:
  `run fw/test_fw.spl` → `ALL FIRMWARE SELF-TESTS PASS` (300 asserts);
  `run fw/sim_main.spl` → `ALL END-TO-END CHECKS PASS`;
  `run fw/nvme_main.spl` → `ALL NVME CONTROLLER E2E CHECKS PASS`.
- **`emu/`** — host-interface ↔ device-interface emulator over a **settable memcpy seam on both
  sides**, ONFI NAND (2×2×2×2×8 = 128 pages), domain newtypes, Lean4 proofs. Gates:
  `run emu/nvme_emu_main.spl` → `EMU E2E PASS` (38 checks; steps 4/5 = fault-inject seam proof);
  4 per-module selftests (116 asserts); `lean emu/proofs/{Addr,Memcpy,Queue,Resource}.lean` exit 0.

Honest caveats: **newtypes are NOT enforced** on this binary (bug filed); the **Lean proofs are
standalone hand-transcribed algorithm models with no mechanical link to executed bytes**; the
Simple firmware was **NOT booted on rv32** (a separate C demo booted = toolchain proof only).

<!-- sdn-diagram:id=nvme_fw_emu_tldr -->
```
  fw/   host SQ/CQ ─► [nvme_admin+qset+controller] ─► HIL ─► FTL ─► FIL ─► ONFI NAND device
  emu/  HOST ──host memcpy──► SharedMem ◄──dev memcpy── DEVICE ─► FTL ─► ONFI NandArray
            (NvmeEmu owns shared + ftl + nand + both DMA ports;  Lean4: Addr/Memcpy/Queue/Resource)
```

Full guide: `nvme_firmware_and_emulator_guide.md`.
