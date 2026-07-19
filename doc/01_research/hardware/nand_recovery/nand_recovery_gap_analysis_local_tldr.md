# NAND recovery/prevention gap analysis (TL;DR)

Maps the taxonomy (`nand_ssd_recovery_prevention_taxonomy.md`) onto this
repo's actual NVMe fw (`examples/09_embedded/simpleos_nvme_fw/fw/`) and
`nand_emu` state. Original headline (still true for what's left): several
mechanisms were **coded but never called in production** — read-retry/vref,
read-disturb scrub, static wear leveling, spare remapping, hot/cold
classification. Others are **physics the emulator can validate but firmware
never uses** — soft sensing (`vt_histogram`/`read_margin` stop at the chip
API), retention/dwell signals (emu-only). RAIN parity works but is DRAM-only,
test-only. LDPC, temperature, 3D-layer, and MLC/TLC families are structurally
out of scope for v1 SLC.

**2026-07-19: the rel_* v1 engine landed and closed most of that list** —
read-retry/vref (`rel_ladder`+`rel_vref`), scrub/WL/spare (`rel_tick`/retire
path), plus new refresh (`rel_refresh`) and disturb tracking (`rel_disturb`),
all wired into production reads/tick/retire (see full doc §1 row annotations
and `rel_wiring_check.spl`). Still open, unchanged: RAIN production wiring,
`hooks.classify_hot`, and the soft-sensing re-export.

Full doc: `nand_recovery_gap_analysis_local.md` — §1 status table (file:line,
with 2026-07-19 annotations), §2 per-family applicability, §3 ranked top-10
opportunities (wiring the 4 unwired mechanisms was #1, now done), §4
out-of-scope with reasons.

<!-- sdn-diagram:id=nand_recovery_gap_pipeline -->
```
2026-07-19: rel_ladder+rel_vref(wired) rel_refresh(wired) rel_disturb(wired)
  scrub_once/wear_level_once/alloc_spare (wired via rel_tick/retire)
  RAIN (still DRAM-only,test-only)   classify_hot (still UNCALLED)
  vt_histogram (still chip-only, not FW-visible)
        │
        ▼ remaining gap = taxonomy minus die-internal/MLC/temp/layer/RAIN-wiring
next: soft-read wrapper(2.4) → age/error-aware GC(3.8) → RAIN wiring(2.8)
  → RFR/RDR-lite classification(2.7)
        │
        ▼ out of scope: LDPC, temperature, 3D layers, MLC/TLC, Vpass/ML
```
