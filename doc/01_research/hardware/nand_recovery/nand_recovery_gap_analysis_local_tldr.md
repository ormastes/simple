# NAND recovery/prevention gap analysis (TL;DR)

Maps the taxonomy (`nand_ssd_recovery_prevention_taxonomy.md`) onto this
repo's NVMe fw (`examples/09_embedded/simpleos_nvme_fw/fw/`) + `nand_emu`
state. Original headline: several mechanisms were **coded but never called in
production** — read-retry/vref, read-disturb scrub, static WL, spare remap,
hot/cold classification. Others are **emu-validated physics FW never used** —
soft sensing (`vt_histogram`/`read_margin` chip-only), retention/dwell
(emu-only). RAIN parity works but is DRAM-only, test-only.

**2026-07-19: rel_* v1 engine landed, closed most of that list** —
read-retry/vref (`rel_ladder`+`rel_vref`), scrub/WL/spare (`rel_tick`/retire
path), plus new refresh (`rel_refresh`) and disturb tracking (`rel_disturb`),
all wired into production reads/tick/retire — see §1 row annotations +
`rel_wiring_check.spl`. Still open: RAIN wiring, `hooks.classify_hot`,
soft-sensing re-export.

Full doc: §1 status table (file:line, 2026-07-19 annotations), §2 per-family
applicability, §3 ranked opportunities (#1 wiring is now done), §4 out-of-scope.

<!-- sdn-diagram:id=nand_recovery_gap_pipeline -->
```
2026-07-19: rel_ladder+rel_vref/rel_refresh/rel_disturb (wired)
  scrub_once/wear_level_once/alloc_spare (wired via rel_tick/retire)
  RAIN (still DRAM-only,test-only)  classify_hot (still UNCALLED)
        │
        ▼ next: soft-read wrapper(2.4) → RAIN wiring(2.8) → RFR/RDR(2.7)
        ▼ out of scope: LDPC, temperature, 3D layers, MLC/TLC, Vpass/ML
```
