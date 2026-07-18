# NAND Recovery & Prevention Taxonomy (TL;DR)
> **Scope:** Foundation research on error recovery and prevention. Canonical backbone: FCR, ROR,
> LaVAR, LI-RAID, WARM, DPES, STRAW, SWEEP, MGC, ColdCode, STAR, CellRejuvo.

**Recovery:** Restore data after initial read fails via ECC decode, Vref sweep, soft sensing,
parity reconstruction, or remapping — up to 10 escalation steps.

**Prevention:** Reduce error creation and delay wear-out via program/erase control, retention
refresh, wear leveling, read-disturb tuning, encoding/placement, bad-block containment.

## Major Families
- **Vref & Sensing:** Vref retry, soft sensing, valley search, LDPC
- **Retention:** Retention-aware read, refresh, HeatWatch, WARM
- **Interference:** Layer/wordline/neighbor-aware, LaVAR, ReNAC, MMI
- **Parity & Die Repair:** RAID/RAIN, LI-RAID, cross-die parity
- **Endurance:** DPES, GuardedErase, AERO
- **Refresh & Reclaim:** STRAW, DEAR, SWEEP
- **Prevention:** Wear leveling, WA reduction, data encoding (MGC, ColdCode)
- **Physical Recovery:** CellRejuvo, self-healing (v2+)

<!-- sdn-diagram:id=nand_recovery_taxonomy -->
```
Read (hard) ──► ECC ──┬─ OK ──► Data
                      └─ FAIL ──► Vref Retry ──► Soft Sense ──► LDPC
                                                                  ↓
                                      ┌──────────────────────────┘
                                      ↓
                              Failure-Mode Aware ──► Parity Repair ──┬─ OK
                                                                      └─ Retire
```
