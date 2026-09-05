# Lane: nvme_emu — pure-Simple NVMe host/device emulator (custom-typed, ONFI NAND, Lean4)

Goal (2026-06-29): pure-Simple impl of an NVMe **host-emulator interface** ↔ **device interface**
with a **settable memcpy/DMA function on both sides**; **ONFI** NAND emulation, **RAM-backed**, geometry
**2ch × 2bank × 2plane × 2block**; **highly custom-typed**; **Lean4 resource + formal verification**.
Built with parallel agents. NO C. Gate: `bin/simple run` (the `check`-blowup bug — use run).

## Geometry (small on purpose)
CHANNELS=2, BANKS_PER_CH=2, PLANES_PER_BANK=2, BLOCKS_PER_PLANE=2, PAGES_PER_BLOCK=8.
→ 16 blocks, 128 physical pages. PPA = (ch,bank,plane,block,page); linear ppn bijective.
Surfaced LBAs ≈ 96 (~75%, rest over-provision). One i64/word stands in for a page payload word.

## Architecture (one owner struct dodges value-semantics sharing)
`NvmeEmu` OWNS the shared DMA region + both ports + FTL + NAND. Host and device never own
separate copies of shared memory (value semantics would diverge); both act on `me.shared`.

<!-- sdn-diagram:id=nvme_emu_stack -->
```
 HOST INTERFACE            SEAM (RAM-backed shared mem)          DEVICE INTERFACE
 HostPort{memcpy fn} --SQ/data via host memcpy--> SharedMem <--via dev memcpy-- DevPort{memcpy fn}
   submit_write/read        SQ | CQ | data buffers (PRP)         dev_step: fetch SQ, DMA data,
   ring doorbell                                                  FTL -> ONFI NandArray, DMA back CQ
                              NvmeEmu owns: shared, host, dev, ftl, nand
```

## Module map (emu/ subdir, all custom-typed)
- `nvme_ct.spl`     — custom domain types via `newtype X = i64` (RESOLVED recon-1): Lba, Ppn, Ch, Bank, Plane, Block, Page, Cid, Qid, Addr, Word. Construct `Lba(value:n)`, unwrap `.value`, arithmetic auto-derived + type-safe (Lba+Ppn = error). SMOKE-TEST on `run` before mass use.
- `nand_onfi.spl`   — `NandArray` 2ch×2bank×2plane×2block, RAM-backed, ONFI cmd protocol + (ch,bank,plane,block,page) decode, multi-plane.
- `nvme_shared.spl` — `SharedMem` (owned byte/word region: SQ|CQ|data), owned-field store/load (interp-safe: writes go to owned fields, never array args).
- `nvme_memcpy.spl` — `MemcpyFn` settable closure seam + default impl (read-slice-and-return; store via owned method). (syntax: TBD recon-3)
- `nvme_host.spl`   — `HostPort`: build SQ entry + data into SharedMem via host memcpy, doorbell, reap CQ + read-data via host memcpy.
- `nvme_device.spl` — `DevPort` + `NvmeEmu`: fetch SQ via dev memcpy, FTL (L2P over ONFI NAND), write CQ+read-data back via dev memcpy.
- `ftl_emu.spl`     — compact custom-typed FTL: L2P map + log append over the ONFI NAND (reuse algorithms from fw/ftl*).
- `nvme_emu_main.spl` — e2e: host writes buffer -> device stores in NAND -> host reads back via the memcpy seam -> verify round-trip + a custom (fault-injecting) memcpy on each side.
- Lean4: proofs of resource + correctness invariants. (mechanism: TBD recon-2)

## Lean4 verification (RESOLVED — recon-2)
Mechanism: annotate PURE functions with `@verify` (`in:` pre, `out(ret):` post, `decreases:` term),
then `simple gen-lean write` → `simple verify check` → `simple verify list`. Lean 4.31.0 installed
(/home/ormastes/.elan/bin/lean); Lake wired; external proofs live under `src/verification/`.
Arithmetic obligations discharge with omega/decide. Provable subset chosen:
- PPA(ch,bank,plane,block,page) <-> ppn **bijection** + in-range (omega/decide) — `nand_onfi` pure addr fns.
- **memcpy length safety**: copy of len N at offset O never exceeds a region (O+N <= region_end) (omega).
- **queue index bounds**: SQ/CQ ring head/tail/len stay in [0,depth] (omega).
- L2P write-then-read **round-trip** (frame-style invariant; NVFS Theorems.lean is the model).
Structure address math + bounds + memcpy-len as pure `@verify` fns so Lean auto-discharges them.

## Foundation — VALIDATED (empirically, this session)
- **newtype** `newtype X = i64`: works on `run` for construct/unwrap/param/return/field/array-of/index.
  DIRECT ARITHMETIC ERASES TO i64 → discipline: unwrap `.value`, math in i64, rewrap. NO compiler
  enforcement (`check` accepts `Ppn`-as-`Lba` AND `Lba+Ppn`) → FILE bug; the typing is documentation +
  structural; real teeth = Lean. Cross-module import prints benign `Unknown type` WARN (run still correct).
- **memcpy seam**: fn-field `copy: fn([i64],i64,i64)->[i64]`; assign a LAMBDA wrapping a named fn
  (`\s,o,n: dma_copy_words(s,o,n)`) — a directly-assigned NAMED fn returns garbage. Pure read-and-return
  (closures can't mutate captures; array-arg writes lost). One owner struct holds shared mem.
- **Lean4**: standalone `.lean` checked with `lean <file>` (PATH=~/.elan/bin), omega/decide. PROVEN: the
  PPA->ppn bound discharges. gen-lean/@verify path is project-scoped + fragile (`in:` fails to parse in a
  loose file; gen-lean --help hangs) → use standalone `.lean` under emu/proofs/, NOT @verify.
- `nvme_ct.spl` LOCKED + smoke-green (128 PPA round-trips + records). `bin/simple run` is the gate.

## DONE (run-green + lean-green, verified in-hand)
- 8 modules + 4 Lean proofs built (parallel agents, against locked nvme_ct).
- Selftests: nand_array(36) + shared_memcpy(25) + ftl(22) + nvme_device(33) = **116 asserts**, ALL EMU SELFTESTS PASS.
- E2E `nvme_emu_main`: **EMU E2E PASS** — host->DMA->FTL->ONFI-NAND->DMA->host round-trip on BOTH channels;
  seam proof: fault-injecting memcpy set on the DEVICE side (step4) AND HOST side (step5) visibly corrupts the
  data path then restores clean → "set memcpy on both sides" is genuinely load-bearing.
- Lean4: Addr/Memcpy/Queue/Resource — **20 theorems, all exit 0, no sorry/admit** (incl. resource: region
  disjointness + use-after-free).
- newtype enforcement gaps filed: doc/08_tracking/bug/newtype_run_path_and_enforcement_gaps_2026-06-29.md.
- "highly custom typed" = newtypes for intent + Lean for enforced guarantees (honest scope in emu/README.md).

## Notes
- rv32 native-boot workflow (prior goal) still finishing; fold in whether pure-Simple natively compiles.
- Land via churn-isolated worktree + SSH non-force push, commit after each batch.
