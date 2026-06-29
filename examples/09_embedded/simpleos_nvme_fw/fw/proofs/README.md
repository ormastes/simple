# NVMe firmware — Lean4 formal verification (`fw/proofs/`)

Standalone Lean4 proofs of the firmware's **safety-critical FTL invariants** (research
requirement 6). Each file checks with `lean <file>` at exit 0 with no `sorry`/`admit`,
using only Lean core + `omega` (no mathlib). The models are hand-transcribed from the
cited Simple sources and the constants match the device geometry (64 blocks × 64 pages =
4096 pages, `GC_RESERVE = 2`); these are proofs *of the algorithms*, not a mechanical
extraction of the executed bytes (same approach as the sibling `emu/proofs/`).

| Proof | Mirrors | Properties proven |
|-------|---------|-------------------|
| `Alloc.lean` | `ftl_band.spl` (`alloc_page`, `alloc_page_host`) | Allocated pages are in range; the write pointer is a strict monotonic cursor (no page handed out twice in a block); the host path never breaches the GC reserve, so GC always has scratch; a non-full victim yields a strict net free-space gain (GC progress). |
| `Recover.lean` | `ftl.spl` (`recover`) | Replaying the journal in append (ascending-seq) order yields, for every LBA, the new_ppn of its **last** record — the committed prefix: newest write wins, a trim clears the LBA unless a later write supersedes it, and an un-journaled LBA stays unmapped. |
| `Gc.lean` | `ftl.spl` (`reclaim_block`) | A relocated page lands **outside** the victim block, so erasing the victim never destroys the current copy of a relocated LBA; a relocation is local (other LBAs untouched); and the abort path (alloc failed → no erase) is a no-op on the map. Together: whether GC succeeds or aborts, no committed data is lost. |

Run all three:

```bash
export PATH="$HOME/.elan/bin:$PATH"
for f in Alloc Recover Gc; do lean examples/09_embedded/simpleos_nvme_fw/fw/proofs/$f.lean && echo "$f OK"; done
```

They are also gated by the system spec
`test/03_system/app/nvme_firmware/nvme_firmware_simulation_spec.spl` (the "Lean4 formal
verification" scenario), alongside the runnable regressions (`gc_safety_check`,
`durability_check`, `wear_scrub_check`) whose assertions these proofs generalize.
