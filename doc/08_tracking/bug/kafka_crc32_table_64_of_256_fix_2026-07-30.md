# kafka crc32_table() 64-of-256 entries fix (2026-07-30)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Flagged (not fixed) in the pass-10 seed root-cause doc as a separate,
pre-existing bug found while verifying the `serialization.spl` list-typed
retype fix. Fixed this pass per the coordinator's priority ("small and
severe, fix first").

## PROVED: empirical failure mode, both engines

`crc32_table()` defined only the first 64 entries of the standard
256-entry CRC-32 (polynomial `0xEDB88320`) lookup table, but
`crc32_calculate` indexes it with `table_idx = (crc ^ byte_val) % 256`
(range 0-255).

- **`SIMPLE_EXECUTION_MODE=interpret`**: hard, bounds-checked crash —
  `error: semantic: array index out of bounds: index is 206 but length is
  64` — the moment any byte drives the lookup index past 63. For
  `crc32_calculate("123456789")` this happens on the very first byte.
- **Default engine**: no crash — silently reads past the array end and
  returns a wrong CRC with no error signal at all:
  `crc32_calculate("123456789")` → `4294967292`,
  `crc32_calculate("a"*100)` → `4294967292` (same garbage value both
  times — consistent with reading a fixed out-of-bounds memory location
  rather than genuinely-random garbage, though this pass did not chase
  the exact mechanism since it's moot once the table is complete).
- Both failure modes reproduced identically on this exact bug (not just a
  hypothetical): empty-string input (`""`) is unaffected either way,
  since the byte loop never executes for zero-length input and the table
  is never indexed at all — matches why earlier round-trip probes in this
  pass's own predecessor (pass 8) never happened to hit it.

## Fix

Regenerated the full, standard 256-entry table via the textbook
bit-reversed CRC-32 construction (polynomial `0xEDB88320`, 256 outer
iterations each running the 8-shift reduction loop) — derived from the
polynomial alone, not copied from any external source. The existing 64
entries were independently confirmed to already be the correct *first* 64
entries of the standard table (byte-for-byte match against the freshly
generated table), so this was purely a truncation, not a wrong-algorithm
bug.

Applied to all 3 real kafka layout tiers (`gc_async_mut`,
`nogc_async_mut`, `nogc_sync_mut` — byte-identical per the pass-9/10
census; `gc_sync_mut` is the known re-export facade, not a real copy).

## Verification (both engines, independent zlib reference, vacuity)

Reference values computed via python3 `zlib.crc32` (IEEE CRC-32,
`zlib.crc32` and the polynomial-table construction implemented here
compute the same standard algorithm):

```
crc32_calculate("")              = 0            (0x00000000)
crc32_calculate("123456789")     = 3421780262   (0xcbf43926)
crc32_calculate("a" * 100)       = 2943384164   (0xaf707a64)
```

The 100-`a` case exercises the ">64-byte payload" class the coordinator
named as the one that currently breaks (its lookup indices sweep well
past the old 64-entry cutoff). All 3 values are byte-exact and identical
under both the default engine and `SIMPLE_EXECUTION_MODE=interpret`
post-fix — no residual engine divergence.

**Vacuity**: swapped the original (64-entry) table back in and re-ran the
identical probe — reproduced both failure modes exactly as described
above (default: silent `4294967292`; interpret: hard crash), confirming
the fix is real, not a probe artifact.

## Integration status: not yet wired into kafka's live record path

Checked whether kafka's record-batch CRC (in `protocol.spl`,
`producer.spl`, `consumer.spl`, `types.spl`, `utilities.spl`) consumes
`crc32_calculate`/`crc32_table`: **it does not.** `grep -rl crc32` across
the kafka module tier matches only `serialization.spl` itself — no other
kafka file calls `crc32_calculate`/`crc32_verify`, and none defines its
own separate CRC32 table. This function exists as a standalone, exported
utility that is not currently on any live record-write/record-read path
in this codebase's kafka implementation. The fix is real and verified at
the unit level (this doc's vectors), but there is no kafka
producer/consumer round-trip to serve as an additional integration proof
— there is nothing upstream calling it yet to prove.

## Campaign status

This closes the crc32_table defect flagged in pass 10. The kafka dedup
retype (pass 10, `serialization.spl`) and this fix are now both landed;
`types.spl`/`protocol.spl`/`consumer.spl`/`producer.spl`/`utilities.spl`
(the larger untyped-`list` sites in kafka) remain open per the pass-9
census fix order.
