# simpleos_nvme_fw — Minimal log-structured FTL prototype

**Simulation only — no hardware, no QEMU, no real MMIO.**  
Host-runnable teaching scaffold for bare-metal NVMe SSD firmware on SimpleOS.

## What it demonstrates

Two complementary files, each runnable independently:

### `main.spl` — Log-structured FTL + P2L crash recovery

- **Simulated NAND** — each page stores a data byte plus OOB metadata
  `{logical addr, write sequence}`
- **Log-structured FTL** — `Ftl` holds an L2P map (lba→ppn), a monotonic write
  sequence counter, and a free-ppn cursor (the log append point)
- **Write path** — `ftl.write(lba, data)` appends a NAND page with OOB, then
  repoints L2P at the new physical page (the old page is left as a stale version)
- **Crash recovery** — `ftl.crash_reset()` zeroes the in-RAM L2P; `ftl.recover()`
  rebuilds it by scanning page OOB and keeping the highest write sequence per LBA
  (a P2L scan — the committed-prefix property in miniature)
- **Offload-op seam** — `offload_checksum(data, lba)` calls a software byte-fold
  fallback; in production this indirection routes to `common.bytes.checksum.Crc32`
  or a hardware CRC engine without changing FTL logic

### `pool_demo.spl` — Generation-checked object pool

- **`TaskPool`** — bounded slots addressed by `Handle{index, generation}` instead of
  a raw pointer
- **Stale-handle guard** — `pool.release(h)` bumps the slot's generation counter;
  any still-live `Handle` is then rejected by `pool.get_phase(h)` and `pool.step(h)`
  (use-after-free equivalent for bare-metal task slots)
- **Cooperative state machine** — `pool.step(h)` advances the slot's phase through
  `PHASE_INIT → PHASE_PROGRAM → PHASE_JOURNAL → PHASE_UPDATE_L2P → PHASE_DONE`;
  state lives in the slot (task context), not on a call-stack local

## How to run

```bash
bin/simple run examples/09_embedded/simpleos_nvme_fw/main.spl
bin/simple run examples/09_embedded/simpleos_nvme_fw/pool_demo.spl
```

Both print per-check `PASS:` lines and a final `PASS` line on success.

## Known issue

`bin/simple check` times out on both files due to a superlinear type-checker blowup
triggered by multiple `me` methods on structs with array fields. The interpreter
(`bin/simple run`) is unaffected — all assertions pass. See:

```
doc/08_tracking/bug/sspec_simple_check_superlinear_two_impls_2026-06-29.md
```
