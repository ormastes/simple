# NVMe firmware build status

Host-runnable simulation, layered HIL → FTL → FIL. Gate: `bin/simple run` (not `check`).
Build workspace: git worktree `simple_nvme_fw_build/` (churn-isolated). Land via worktree
commit → rebase onto origin/main (adds-only) → non-force SSH push.

## Done (run-green, on origin/main)
- `nvme_types.spl` — frozen shared interface (constants, Handle, NvmeCmd/Cpl, helpers, expect_eq).
- **FIL complete**: `fil_nand` (sim NAND), `fil_ecc`, `fil_badblock`, **`fil.spl`** (NAND+ECC+bad-block remap, page API for FTL; `FilRead{data,lba,seq,code}`).
- **FTL leaves**: `ftl_map` (DFTL write-back cache), `ftl_band` (log allocator + valid bitmap), `ftl_journal` (WAL+checkpoint+A/B superblock).
- **HIL+core leaves**: `hil_queue` (SQ/CQ rings), `hil_command` (decode/validate), `fw_pool` (gen-handle task pool; accessors cid/lba/data/status/old_ppn/new_ppn/seq/phase).
- `test_leaves.spl` runs all 9 leaf self-tests (176 assertions). `CONVENTIONS.md`, bug docs.

## Architecture decisions (verified)
- **Nested struct field-method mutation PERSISTS**: `me.field.method(...)` mutates the field in
  place (tested). So compose cleanly: `Fil{nand,bbt}`, `Ftl{fil,map,band,journal,seq}`,
  `Hil{queues,ftl,pool}`, `Firmware{hil}` — methods call `me.fil.program(...)` etc. directly.
- **Value semantics**: structs copy on assignment; mutate only via `me.field` / `me.field.method`.
- **Conditional first-param ×8 interp bug**: isolated to `ftl_journal.append` (dummy `_p0`
  leading param; callers pass 0). Every multi-param `me` method's self-test must round-trip
  each stored value. See `CONVENTIONS.md`.

## Integration — COMPLETE (run-green, end-to-end verified, on origin/main)

All layers implemented and verified. `test_fw.spl` = **225 self-test assertions** across 14
modules; `sim_main.spl` = full end-to-end (128 writes → read-back → overwrite/GC → trim →
power-fail + recovery) — all green via `bin/simple run`.

- **`ftl.spl`** — `Ftl{fil,map,band,journal,seq}`: `write` (alloc → fil.program → journal →
  map.update → mark_valid + invalidate old), `read`/`read_status`, `trim`, `checkpoint`,
  `crash`, `recover` (WAL replay, newest-seq wins), `gc_once` (transactional relocate→erase).
- **`ftl_gc.spl`** — `gc_select_victim(band)` greedy (CLOSED block, fewest valid pages).
- **`hil.spl`** — `Hil{q,ftl,pool}`: `submit`, `tick` (fetch SQ → validate → dispatch behind a
  `fw_pool` WriteTask state machine → post CQ), `run`, `reap`, `gc`/`crash`/`recover`.
- **`firmware.spl`** — `Firmware{hil}` cooperative reactor: `service` (drain queues + background
  GC below the free-block watermark), `gc_sweep`, `checkpoint`, `power_cycle`, `reap_all`.
- **`sim_main.spl`** — the production end-to-end gate (`fn main()`).
- **`test_fw.spl`** — full self-test suite. `README.md` — architecture + requirements coverage.

Deferred to the build plan (not part of this firmware's run-green core): Lean4 proofs (req 6)
and sandboxed dynamic policy hooks (req 7); multi-channel scheduling + static wear leveling are
natural next extensions (dynamic wear leveling is implicit in the log-structured write path).
