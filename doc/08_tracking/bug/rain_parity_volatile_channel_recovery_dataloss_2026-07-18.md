# RAIN channel recovery is not power-cycle safe (parity table is volatile)

## Symptom

`Ftl.rain_recover_channel(failed)` in
`examples/09_embedded/simpleos_nvme_fw/fw/ftl.spl` rebuilds a failed NAND
channel by reconstructing each stripe from `sealed parity XOR surviving
channels`, then erasing the failed block and reprogramming its live pages in
place (raw `me.fil.erase` / `me.fil.program`, bypassing the allocator/journal so
the L2P ppns stay fixed).

The reconstruction depends on `me.rain_parity`, which is an **in-DRAM** `[i64]`
table maintained live on the write path (`rain_update_page`,
`rain_note_erased_block`). It is never persisted to media, and `recover()` does
not rebuild it. `crash()` also does not clear it, unlike its DRAM peers
(`map` write-back cache, `band` bitmap, `rd_disturb`) — so the model currently
*masks* the loss rather than modeling it.

Consequence on real hardware: if power is lost after a channel fails and before
`rain_recover_channel` completes (e.g. between the erase and the in-place
reprogram), the failed channel's live pages are permanently lost. The survivors
are durable NAND, but the parity word needed to reconstruct them is gone from
DRAM and cannot be re-derived — `rain_seal` would read the failed/erased
channel's own garbage and produce wrong parity for exactly those stripes.

## Root cause

RAIN parity is modeled as a volatile DRAM table instead of on-media parity
(real RAID-4/RAIN keeps parity on the media). Because the parity is not durable
and is not reconstructable after a channel has already failed, RAIN cannot
protect against a *persistent* channel failure that spans a power cycle — which
is the feature's stated purpose.

## Scope / severity (why not fixed here)

Low, currently latent: `rain_recover_channel` and `rain_seal` are **not wired
into any production path** (nvme_admin / nvme_controller / firmware / hil /
reactor). They are test-only capabilities invoked from `ftl_rain_selftest`;
only the incremental parity maintenance runs in production. The model also
cannot express a mid-`rain_recover_channel` crash (`crash()` is only callable
between top-level FTL ops), so the window is not reachable in-model today.

The genuine root fix is on-media parity persistence (allocate parity blocks,
persist on `checkpoint()`, restore in `recover()`), a substantial FTL feature —
inappropriate to bolt onto this low-severity, test-only path, and it would touch
`ftl_journal`/`ftl_band`/geometry. Partial fixes suggested for a copy window
(stage-to-spare, route-through-allocator) do NOT apply: source and destination
are independent here (the source is the already-failed channel), so staging is
pointless and allocator-routing breaks the in-place-ppn invariant.

The `rain_recover_channel` doc comment was amended to state this precondition
honestly so the next reviewer does not re-flag it as copy-atomicity or paper
over it with a "safe" note.

## Fix direction

- Persist RAIN parity to media (on-media parity blocks) and restore it in
  `recover()`; on a clean power cycle with all channels healthy, `recover()` may
  reseal from durable NAND, but a failed channel requires parity sealed *before*
  the failure, hence the on-media requirement.
- Make `crash()` clear `me.rain_parity` (fidelity) once a durable restore path
  exists, so the volatile-loss model is honest.
- Wire recovery into a host/admin or background path if RAIN is to be a live
  production feature, not a demonstrated capability.

## Regression to add on fix

In `durability_check.spl` (or `rain_ftl_check.spl`): write known data, fail a
channel, `crash()` + `recover()`, then `rain_recover_channel(failed)` and assert
every LBA reads back its original value (no data loss across the power cycle).
Also assert a mid-recovery power loss (erase done, reprogram not) recovers with
no loss once parity is durable.
