# NAND recovery/prevention gap analysis (TL;DR)

Maps the taxonomy (`nand_ssd_recovery_prevention_taxonomy.md`) onto this
repo's actual NVMe fw (`examples/09_embedded/simpleos_nvme_fw/fw/`) and
`nand_emu` state. Headline: several mechanisms are **already coded but never
called in production** — read-retry/vref, read-disturb scrub, static wear
leveling, spare remapping, hot/cold classification. Others are **physics the
emulator can validate but firmware never uses** — soft sensing
(`vt_histogram`/`read_margin` stop at the chip API), retention/dwell signals
(emu-only). RAIN parity works but is DRAM-only, test-only. LDPC, temperature,
3D-layer, and MLC/TLC families are structurally out of scope for v1 SLC.

Full doc: `nand_recovery_gap_analysis_local.md` — §1 status table (file:line),
§2 per-family applicability, §3 ranked top-10 opportunities (wiring the 4
unwired mechanisms is #1), §4 out-of-scope with reasons.

<!-- sdn-diagram:id=nand_recovery_gap_pipeline -->
```
status-quo: ECC(wired) ─ vref-actuator(wired,no policy)
  scrub_once/wear_level_once/alloc_spare/classify_hot (coded, UNCALLED)
  RAIN (DRAM-only,test-only)   vt_histogram (chip-only, not FW-visible)
        │
        ▼ gap = taxonomy 2.1-2.10/3.1-3.11 minus die-internal/MLC/temp/layer
v1 target: wire-4-unwired → retry-ladder(2.1) → ROR-lite(2.2)
  → STRAW-lite(3.4) → FCR/DEAR-lite(3.3) → SREA-lite WL(2.10)
  → soft-read wrapper(2.4) → age/error-aware GC(3.8) → RAIN wiring(2.8)
        │
        ▼ out of scope: LDPC, temperature, 3D layers, MLC/TLC, Vpass/ML
```
