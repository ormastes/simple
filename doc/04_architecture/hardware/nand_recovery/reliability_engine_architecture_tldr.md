# Reliability Engine Architecture (TL;DR)

**LAW:** shared reliability logic = layer-neutral `rel_*` modules placeable on FTL
OR FIL; only L2P/hotness/GC-dependent logic is FTL-pinned. Decision and actuation
are **separate axes** — the verdict seam decouples them.

- **`rel_*` family (pure, below `fil`, `use nvme_types.*` only):** `rel_types`
  (RelAction verdict enum + obs/state structs + mount bundles), `rel_ladder`
  (retry escalation), `rel_vref` (ROR-lite), `rel_refresh` (FCR/DEAR-lite),
  `rel_disturb` (STRAW-lite), `rel_wear` (SREA-lite), `rel_health` (RBER/corrected-bit).
- **Mounts = pure state bundles composed by the layer** (no policy holds a handle):
  `RelFilMount` (Vref retry inside `fil.read`), `RelFtlMount` (refresh/reclaim/WL in service tick).
- **Actuation = verdicts:** `RetryAtOffset·CalibrateBlock·MarkForRefresh·ReclaimNow·Quarantine·Uncorrectable`.
  Rewires today's immediate `NAND_ECC_FAIL` (gap A2) into a Vref sweep.
- **Wiring:** the 4 unwired mechanisms (scrub/wear_level/rain_seal/alloc_spare) into
  the tick under **one reclaim-class step/tick, total** (they share `GC_RESERVE`).
- **Prereq seams:** `FilRead.corrected`, `fil.read_at_vref`, re-export emu
  `vt_histogram`/`read_margin`.
- **v1** = SLC ladder+ROR+FCR/DEAR+STRAW+SREA+wiring; **v2** = soft-LDPC/LaVAR/ReNAC/temp (emu must grow).

```
<!-- sdn-diagram:id=rel_engine_tldr -->
FTL tick ─► RelFtlMount{refresh,disturb,wear} ─┐
                                               ├─► rel_* PURE (verdict-returning, NO handle) ─► nvme_types
fil.read ─► RelFilMount{vref,ladder,health} ───┘        RelAction: Retry/Calibrate/Refresh/Reclaim/Quarantine
   ECC-FAIL ─► ladder ─► RetryAtOffset(Vref sweep) ─► OK → CalibrateBlock ; exhausted → parity → Quarantine
```
