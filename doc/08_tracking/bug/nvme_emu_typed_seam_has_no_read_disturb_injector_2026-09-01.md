# The typed emu_* seam has no read-disturb injector, so read-disturb recovery is untestable

- id: nvme-emu-no-read-disturb-injector-2026-09-01
- date: 2026-09-01
- area: examples/09_embedded/simpleos_nvme_fw/fw (fil_nand_emu / fil / ftl emu_* test-control seam)
- severity: medium — a whole NAND failure mode (read disturb) has no system-level
  recovery test, and cannot get one without either a new seam entry point or a
  ~7-minute test.
- status: open

## Summary

The typed test-control seam threaded FTL → FIL → FMC → NandEmu exposes exactly
five entry points: `emu_advance_time_s`, `emu_set_block_wear`,
`emu_set_vref_offset`, `emu_vt_histogram`, `emu_read_margin`
(`fw/ftl.spl:265-282`, `fw/fil.spl:282-302`, `fw/fil_fmc.spl:229-261`).

None of them injects read disturb. The only way to raise a page's `rd_count` is
to issue real reads, and the physics makes that infeasible for a test:

- `src/lib/hardware/nand_emu/physics.spl` `ne_disturb_delta`:
  `delta = rd_coef * rd_count / 10000 + pd_coef * pd_count / 200`
- profile S1 (`nand_types.spl:122`) `rd_coef = 1.0` → **+1 Vt code per 10,000
  neighbour reads**
- an erased cell sits at `erase_mean = 88` against a default reference of 128, so
  a flip needs ~40 codes ⇒ **~400,000 neighbour senses**

Polarity note: disturb pushes Vt **up**, retention pushes programmed cells
**down**. They cannot be stacked — the victim of a disturb fault must be erased
bits, the victim of retention must be programmed bits — so retention cannot be
used to shorten the loop.

## Evidence (measured 2026-09-01, `bin/simple run`, Rust seed)

`examples/09_embedded/simpleos_nvme_fw/fw/nvme_emu_read_disturb_probe_check.spl`
hammers a genuine same-block page neighbour over the ordinary NVMe path (run below used HAMMER_READS = 2000; the committed probe uses 500 to stay inside the 10s example cap — the verdict is identical either way):

```
  victim WRITE lba8 status=0
  hammer WRITE lba9 status=0
  victim ppn=0 blk=0 page=0
  hammer ppn=1 blk=0 page=1
  victim raw byte before hammering = 255
  issued 2000 host reads of the neighbour
  victim raw byte after hammering  = 255
READ DISTURB PROBE DID NOT MOVE: 2000 neighbour reads left the victim unchanged; the typed seam has no disturb injector and the physics needs ~400000 senses
error: example timed out after 10s
real 0m11.132s
```

Adjacency is real (same block, pages 0 and 1), so the hammering is not vacuous —
the fault simply cannot reach threshold. 2,000 host reads cost ~6s of run time
after startup; each host read costs two senses (`read_range_status` probe +
`ftl.read`), so ~200,000 host reads are needed ⇒ **~10 minutes**, against a
harness cap that killed this probe at 10s.

## Why this is filed instead of tested

`nvme_emu_recovery_check.spl` covers retention drift, wear-induced ECC pressure,
and unrecoverable damage. A read-disturb scenario was scoped alongside them and
deliberately NOT written: any assertion it could make within the time budget
would be an assertion that cannot fail.

## Suggested fix (not applied — reporting only)

Add one typed entry point, symmetric with `emu_set_block_wear`:

```
me emu_set_read_disturb(ppn: i64, rd_count: i64)
```

threaded FTL → FIL → FMC → `NandEmu` → `NePageMeta.rd_count`. That is the same
shape as the existing wear injector, keeps fault injection inside the typed seam
(no `.nandram` poking), and makes a read-disturb recovery scenario a
sub-second test.

## Repro

```
bin/simple run examples/09_embedded/simpleos_nvme_fw/fw/nvme_emu_read_disturb_probe_check.spl
```
Verdict token: `READ DISTURB PROBE DID NOT MOVE: ...`
