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

All layers implemented and verified. `test_fw.spl` = **295 self-test assertions** across 22
modules; `sim_main.spl` = full single-queue end-to-end (128 writes → read-back → overwrite/GC →
trim → power-fail + recovery); `nvme_main.spl` = the admin-driven controller e2e (27 asserts) —
all green via `bin/simple run`.

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

## NVMe controller front end — COMPLETE (admin + multi IO queue + ONFI NAND)

The full-controller layer, on top of the FTL/FIL stack (legacy single-queue
`hil.spl`/`firmware.spl` left untouched so its assertions stay the regression gate):

- **`nvme_admin_types.spl`** — admin opcodes, CNS/feature/log ids, admin status codes,
  `AdminCmd{cid,opcode,nsid,cdw10..12}`, `IdentifyData`, `SmartLog` (types only, no `me`).
- **`nvme_admin.spl`** — `AdminQueue` (qid-0 SQ/CQ rings), `FeatureStore` (Get/Set Features),
  command-dword decoders + `AdminCmd` builders, Identify Controller/Namespace + SMART builders.
- **`nvme_qset.spl`** — `QueueSet`: up to `MAX_IO_QUEUES` IO SQ/CQ pairs in flat parallel
  arrays (ring of qid q at offset `q*MAX_QUEUE_SIZE`). Enforces NVMe-faithful semantics:
  CQ-before-SQ, SQ binds to an existing CQ (`SC_CQ_INVALID`), no delete of a CQ with a bound
  SQ (`SC_QUEUE_BUSY`), qid range / in-use / size checks; fair round-robin `next_pending_sq`.
- **`nvme_controller.spl`** — `NvmeController{aq,qset,features,ftl,pool,last_id,smart,…}`:
  `admin_process` (Create/Delete IO SQ/CQ, Identify, Get/Set Features, Get Log Page) and
  `io_process` (round-robins active SQs → FTL → FIL, posts to each SQ's bound CQ).
- **`fil_nand_device.spl`** — protocol-accurate ONFI NAND *device* model: CMD/ADDR/DATA latch +
  `exec()` state machine (READ 00h/30h, PROGRAM 80h/10h main+spare, ERASE 60h/D0h, STATUS 70h,
  RESET FFh), status register (FAIL/ARDY/RDY/WP_N), OOB {lba,seq} spare area, no-overwrite rule,
  per-page bit-flip injection, bad-block + one-shot program/erase fault injection. **Faithful
  drop-in for `fil_nand.Nand`** — same `program/read_page/erase_block/erase_count/inject_*/set_bad`
  seam, each driving the ONFI bus internally.
- **`nvme_main.spl`** — the controller acceptance e2e: host bring-up (Identify → Features →
  Create CQ→SQ) → multi-queue IO + round-robin → negative cases (SQ→missing-CQ, delete-bound-CQ)
  → reverse-order teardown → SMART log → power-cycle survival.

**The FIL runs on the ONFI device** (plan phase E3, done): `fil.spl` composes `NandDevice` (not the
behavioural `fil_nand.Nand`), so every write/read/GC-erase/recovery-OOB-scan in `sim_main` and
`nvme_main` goes through the real ONFI handshake. `fil_ecc` keeps the FIL-level ECC (the device
reports the injected bit-flip count; FIL decides OK/FIXED/FAIL). 300 self-test assertions green.

Scope note (explicit): "full NVMe SSD fw" here = the host-runnable simulation (run-green).
Bare-metal **rv32** boot of *this Simple firmware* is the no-alloc follow-up (`[i64]`/`.push`
needs a heap); a self-contained C NAND/FTL demo already boots on `qemu-system-riscv32 -bios none`
(`ALL RV32 NAND CHECKS PASS`) as current proof of the toolchain + boot path.

## Production hardening — DONE (run-green, on origin/main)

See `PRODUCTION_STATUS.md` for the acceptance bar. Landed since the initial build:
- **Data-path correctness**: GC data-loss guard (a victim is erased only after every live page
  is relocated), a GC scratch reserve eliminating the write-cliff, and no silent journal-record
  drop on WAL overflow. Regressions: `gc_safety_check.spl`, `durability_check.spl`.
- **Faithful durability**: power loss wipes all volatile DRAM (map cache + band bitmap); recovery
  replays the journal onto the flash-resident L2P, rebuilds the band, and re-applies the
  persistent bad-block table.
- **Protocol surface**: overflow-safe command validation (correct `SC_*`, no crash) + the
  mandatory admin set (Abort, Async Event Request, Format NVM, Firmware Download/Commit).
- **Media management**: static wear-leveling (`wear_level_once`) + read-disturb scrub (`scrub_once`).
- **Health**: SMART wired to real activity (wear, spare, media errors, unsafe shutdowns) + error log.
- **Formal (req 6) — DONE**: `proofs/{Alloc,Recover,Gc}.lean` (`lean`-checked).

Still deferred (per the build plan): sandboxed dynamic policy hooks (req 7); multi-channel
scheduling; and the silicon-only pieces (real BCH/RS hardware ECC, MMIO/PCIe, persistent backing
store) — see `PRODUCTION_STATUS.md` § Silicon boundary and the bare-metal rv32 port note above.
