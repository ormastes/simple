# Recovery Algorithms Detail Design — TL;DR

v1 detail design for the `rel_*` policy family (pure leaf under `fil`; verdict =
`RelAction {kind,arg}` tagged struct; per-block `[i64]` state, len `NUM_BLOCKS`=64).
Six algorithms + wiring, each with fields/sizes, Simple pseudocode (i64-first,
return-the-object, no Dict), constants, mount, and a nand_emu oracle.

- **Ladder** (§1/§2.1): hard→SECDED→calibrated-seed→7-entry table walk→`Uncorrectable`; RAIN/Quarantine actuated by the FTL caller. Mount **FIL**.
- **Vref/ROR-lite** (§2.2): 7-entry retention-biased table + per-block offset cache, decay-on-erase. Mount **FIL**.
- **Refresh/FCR+DEAR-lite** (§3.3): triggers = needed_retry / corrected-events≥3 / seq-age proxy. Mount **FTL**.
- **Disturb/STRAW-lite** (§3.4): extends existing `rd_disturb` + Boyer-Moore hottest-page → `ReclaimNow`. Mount **FTL**.
- **Wear/SREA-lite** (§3.7): erase-spread + erase-count-delta dwell → static WL. Mount **FTL**.
- **Wiring**: one reclaim-step/tick (GC>refresh>scrub>WL, shared `GC_RESERVE`=2), `rain_seal` own bound, `alloc_spare` event-driven from retire.

Validation pins retention at **~5 K P/E** (30 K/1 yr saturates per emu note). Primary
oracles run today; `vt_histogram`/`read_margin` oracles need the wrapper re-export seam.

```
<!-- sdn-diagram:id=rel_ladder_and_mounts -->
 fil.read FAIL ─► rel_ladder: seed(cache) ─► table[-8,-16,+8,-24,+16,-32,+24] ─► OK?
        │                                                     │            │
        ▼ RetryAtOffset (set_vref_offset, GLOBAL 128+k)       ▼ CalibrateBlock (ROR cache)
   read_at_vref ── loop ──────────────────────────►  exhausted ─► Uncorrectable
                                                          │
   RelFilMount{vref,health*,ladder}  (FIL)                ▼  ftl.read escalates
   RelFtlMount{refresh,disturb,wear,health} (FTL) ─► RAIN reconstruct ─► Quarantine ─► alloc_spare
   FTL tick: rel_tick_select ─► ONE of gc/refresh/scrub/wl per tick     (*FIL health = transient)
```
