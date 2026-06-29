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

## TODO (integration, in order)
1. **`ftl.spl`** — `struct Ftl{fil:Fil, map:L2pMap, band:BandAlloc, journal:Journal, seq:i64}`;
   `me write(lba,data)` (alloc_page → fil.program → journal.append(0,…) → map.update →
   band.mark_valid + invalidate old), `me read(lba)->i64`, `me trim(lba)`, `me recover()`
   (clear map, replay journal / P2L-scan newest-seq), plus GC + wear (below). `ftl_selftest`.
2. **`ftl_gc.spl`** — `fn gc_select_victim(band)->i64` (greedy: CLOSED block, fewest valid);
   the page-move + erase as an `Ftl` method (`me gc_once()`), transactional (new durable before
   old freed). Test crash-during-GC keeps data.
3. **`ftl_wear.spl`** — dynamic + static wear leveling helpers (free fns on band/erase counts).
4. **`hil.spl`** — `Hil{queues,ftl,pool}`; `me submit(cmd)`, `me tick()` (fetch SQ → validate →
   dispatch to ftl via a fw_pool WriteTask state machine → post CQ), `me reap()->NvmeCpl`.
5. **`firmware.spl`** — top-level wiring + cooperative reactor (`me run_until_idle()`, watchdog).
6. **`sim_main.spl`** — END-TO-END demo (has `fn main()`): host workload (writes/reads/overwrite/
   trim) → assert read-back → inject crash (drop RAM map) → `recover()` → assert committed
   survives → trigger GC → assert logical view preserved + free reclaimed. THE production gate.
7. Tests: `test_ftl.spl`, `test_e2e.spl`; update top-level `README.md`.
