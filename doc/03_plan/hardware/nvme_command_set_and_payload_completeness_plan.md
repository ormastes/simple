# NVMe Command Set and Payload Completeness Plan (Workstream D)

Spine: `doc/03_plan/hardware/nvme_complete_fw_mdsoc_offload_master_plan.md` §5.
Staged scope inherited from `doc/03_plan/hardware/nvme_ssd_firmware_hardening_design_plan.md` §6.1.
Subject tree: `examples/09_embedded/simpleos_nvme_fw/fw/` (73 `.spl` files in `fw/`, 287 across the example).

---

## 0. Prerequisite zero, verified

`examples/09_embedded/simpleos_nvme_fw/fw/nvme_types.spl:98`

```
    data:    i64   # simulated single-byte payload stand-in
```

The entire host data path carries **one machine word per LBA**. There is no
page, no OOB payload, no metadata region, no ECC codeword — only a scalar.

**The contradiction is already on record in the firmware's own Identify
response.** `nvme_admin.spl:109` hand-writes:

```
    ... nsid: nsid, ns_size: LBA_COUNT, ns_cap: LBA_COUNT, lba_bytes: 4096)
```

and `nvme_admin.spl:612` asserts it (`"identify-namespace block size 4096"`).

> **Resolved 2026-09-01 (with D1-D3).** Both literals now read `LBA_BYTES` from
> `nvme_payload.spl`, and the selftest gained two anti-drift oracles tying the
> advertised block size to the real media width
> (`ins.lba_bytes == PAGE_BYTES / LBAS_PER_PAGE` and
> `PAGE_WORDS * WORD_BYTES == ins.lba_bytes`). The 512x over-claim is gone: the
> media genuinely stores `PAGE_BYTES` per page as of D3.
The device advertises a **4096-byte** logical block while its media stores
**8 bytes** per page. That is a 512x over-claim, and it is exactly the failure
mode §6.1 forbids: *"Unsupported commands and features must be reported
accurately."* Section 3 of this plan exists because of that one line.

The same decorative-width pattern repeats in DRAM: `dram.spl:10` declares
`WRITE_BUFFER_ENTRY_BYTES: i64 = 4096`, but the arena it sizes is
`DramWriteBuffer.data: [i64]` of `WRITE_BUFFER_CAP_BLOCKS = 16` **slots**
(`dram.spl:29-30`, `dram.spl:41`) — one word per "4096-byte" entry. The byte
constant is never multiplied by anything.

### 0.1 Blast radius (file:line)

Host command / completion — the source of the stand-in:

| Site | What it is |
|---|---|
| `nvme_types.spl:98` | `NvmeCmd.data: i64` — **the declaration** |
| `nvme_types.spl:100`, `:103` | `cmd_make` / `cmd_make_nsid` constructors thread it |
| `nvme_types.spl:113` | `NvmeCpl.data: i64` — read result, one word |
| `nvme_types.spl:115` | `cpl_make` |

Host interface layer:

| Site | What it is |
|---|---|
| `hil_command.spl:40` | zero-payload validation for FLUSH (`c.data != 0`) |
| `hil_command.spl:57,59,61` | TRIM / WRITE_ZERO / READ reject non-zero `data` |
| `hil_command.spl:67-76` | `PRP_SEG_BLOCKS`, `prp_pack`, `prp_first_base`, `prp_second_base` — **`data` is simultaneously overloaded as a packed two-byte PRP descriptor** (`c.data & 0xFF`, `(c.data >> 8) & 0xFF`) |
| `hil.spl:45` | `rdata: i64` accumulator |
| `hil.spl:155,193,254`, `dram_buffer_check.spl:18,33` | callers packing payload through `prp_pack` |
| `hil_queue.spl:98` | `me.sq_data[t] = c.data` — submission ring is a word array |
| `hil_queue.spl:161` | `me.cq_data[t] = p.data` — completion ring likewise |

Controller / admin:

| Site | What it is |
|---|---|
| `nvme_controller.spl:414` | `var rdata: i64 = 0` |
| `nvme_controller.spl:422` | `me.pool.acquire(cmd.cid, cmd.lba, cmd.nblocks, cmd.data)` — in-flight task pool stores the word |
| `nvme_controller.spl:158`, `:479` | `cpl_make(..., r.data)` / `cpl_make(cmd.cid, status, rdata)` |
| `nvme_admin.spl:109`, `:123` | `lba_bytes: 4096` hand-written into Identify (see above) |

FTL:

| Site | What it is |
|---|---|
| `ftl.spl:144` | `me write(lba: i64, data: i64) -> i64` |
| `ftl.spl:189` | `me read(lba: i64) -> i64` — returns the word |
| `ftl.spl:247` | `me trim(lba: i64)` — no payload to invalidate |

FIL / FMC / NAND:

| Site | What it is |
|---|---|
| `fil.spl:28` | `FilRead.data: i64` |
| `fil.spl:62,65` | `rel_read_result_ok/fail(data: i64, ...)` |
| `fil.spl:104` | `me program(ppn, lba, seq, data: i64)` |
| `fil.spl:129-130`, `:144-145` | `ecc_decode(res.data, ...)` then `FilRead(data: dec.data, ...)` |
| `fil.spl:275` | `me corrupt_page_data(ppn, data: i64)` — fault injection is word-wide |
| `fil_fmc.spl:38,40` | `FmcCmd.data: i64`, `fmc_cmd(...)` |
| `fil_fmc.spl:46` | `FmcResult.data: i64` |
| `fil_fmc.spl:89,131,136,170,172,217` | FMC program/read/corrupt path |
| `fil_nand.spl:18` | `Nand.data` — the media array itself, one word per PPN |
| `fil_nand.spl:67` | `Nand(...)` constructor — **note the parallel `oob_lba` / `oob_seq` / `oob_ecc` arrays already exist** |
| `fil_nand.spl:79,92` | `program` → `me.data[ppn] = data` |
| `fil_nand.spl:95` | `me.oob_ecc[ppn] = ecc_compute(data, lba, seq)` |
| `fil_nand.spl:101,105` | `NandRead(data: me.data[ppn], ...)` |
| `fil_nand.spl:119` | erase → `me.data[ppn] = 0` |
| `fil_nand.spl:157-160` | `corrupt_page_data` |
| `fil_nand_device.spl:246,317` | mirrored `program` / `corrupt_page_data` |

ECC — the reason workstream A is blocked:

| Site | What it is |
|---|---|
| `fil_ecc.spl:13` | `EccDecode.data: i64` |
| `fil_ecc.spl:33` | `ecc_hamming_payload(data: i64)` — Hamming over **one word** |
| `fil_ecc.spl:68,73,81,114` | `ecc_compute` / `ecc_flip_data_pos` / `ecc_decode` / `ecc_check` |

RAIN (die-level parity) — also fake-width:

| Site | What it is |
|---|---|
| `rain.spl:32,37,41` | `Rain.data` is one word per channel |
| `rain.spl:53,59` | parity is `xor_all` over `NUM_CHANNELS` **words**, not pages |

DRAM:

| Site | What it is |
|---|---|
| `dram.spl:10` | `WRITE_BUFFER_ENTRY_BYTES = 4096` (decorative) |
| `dram.spl:29-30` | `DramWriteBuffer.data: [i64]`, 16 slots |
| `dram.spl:41` | `dram_write_buffer_new` fills 16 word slots |
| `dram.spl:182` | `expect_eq(b.cap * WRITE_BUFFER_ENTRY_BYTES, ...)` — the budget is asserted **symbolically**, never against the real arena width |
| `dram.spl:101,121,146,164` | slot clear / write / read — `me.data[slot] = byte & 0xFF` |

Test/check files pinned to the stand-in (they encode the defect as expected
behaviour and must migrate with their layer): `fil_ecc.spl:192,198`,
`fil_nand.spl:178,185,242`, `fil_nand_device.spl:341,349,355,363,379,401,421`,
`fil.spl:316,325,333`, `fil_fmc.spl:300`, `ecc_check.spl:20,31`,
`dram_buffer_check.spl:31`, `hil_queue.spl:295`,
`nvme_emu_media_check.spl:63,70,94,108,118`,
`nvme_controller.spl:687,700-702,711,723,734,747`, `nvme_main.spl:96,123-124,165-166`,
`firmware.spl:265,273`.

**Conclusion.** ~90 sites across 20 files. Every "page", "codeword", "PRP",
"parity" and "4096-byte block" claim in this firmware is currently a claim about
a single `i64`.

---

## 1. Payload widening design

### 1.1 Profile constants

The profile the tree already half-assumes in three independent places
(`nvme_admin.spl:109` `lba_bytes: 4096`, `dram.spl:10`
`WRITE_BUFFER_ENTRY_BYTES = 4096`, `nvme_admin.spl:612`). Make it real, and
declare it once in `nvme_types.spl` beside the existing geometry block
(`nvme_types.spl:43-49`):

```
val LBA_BYTES:        i64 = 4096   # logical block size — MUST equal Identify lba_bytes
val PAGE_BYTES:       i64 = 4096   # NAND page main area
val LBAS_PER_PAGE:    i64 = 1      # 1:1 for this profile; the only ratio P0-P2 support
val WORD_BYTES:       i64 = 8
val PAGE_WORDS:       i64 = 512    # PAGE_BYTES / WORD_BYTES
val OOB_BYTES:        i64 = 128    # spare area: metadata + ECC parity
val CODEWORD_BYTES:   i64 = 1024   # 4 codewords per page
val CODEWORDS_PER_PAGE: i64 = 4
val PARITY_BYTES_PER_CODEWORD: i64 = 16
```

Rationale for 1 LBA per page: it keeps the existing L2P map (`ftl_map.spl`) a
straight LBA→PPN table, so **no FTL mapping change is required by the widening
itself**. Sub-page LBAs (512B) would force read-modify-write and a partial-page
allocator; that is deliberately deferred to P3 and must not be smuggled in here.
`LBA_COUNT = 3072` (`nvme_types.spl:48`) and `NUM_PAGES = 4096`
(`nvme_types.spl:47`) already stand in a 1:1-with-overprovision relation, which
confirms the ratio the tree was written for.

### 1.2 Types

Introduce these in a new `fw/nvme_payload.spl`, imported by `nvme_types.spl`
so every layer sees one definition:

```
struct PageData:            # main area, PAGE_WORDS words
    words: [i64]

struct OobData:             # spare area — folds the EXISTING parallel arrays
    lba:    i64             # was Nand.oob_lba   (fil_nand.spl:67)
    seq:    i64             # was Nand.oob_seq   (fil_nand.spl:67)
    parity: [i64]           # was Nand.oob_ecc   (fil_nand.spl:67), now per-codeword
    meta:   [i64]           # host metadata / DIF-PI region, MetadataLayout-shaped

struct CodewordSpan:        # a slice of PageData + its parity, the ECC unit
    page_word_off: i64      # 0, 128, 256, 384 for CODEWORD_BYTES=1024
    word_count:    i64
    parity_index:  i64      # index into OobData.parity

struct MetadataLayout:      # declares what OobData.meta MEANS, per namespace
    ms_bytes:      i64      # Identify NS "metadata size"; 0 = disabled
    pi_type:       i64      # 0 = none; 1/2/3 = DIF/PI types (P3)
    pi_first:      bool     # PI in first/last 8 bytes of meta
```

`OobData` is not new structure — it is a *renaming and completion* of what
`fil_nand.spl:67` already carries as three loose parallel arrays. That is the
cheapest part of the migration and should land first.

`CodewordSpan` is the type workstream A's ECC offload needs. Today
`fil_ecc.spl:33` computes Hamming over a single `i64`; with `CodewordSpan` the
same entry point becomes `ecc_compute(span: CodewordSpan, page: PageData, oob:
OobData)` and the offload has a real, fixed-size buffer to DMA.

### 1.3 DRAM write buffer

`DramWriteBuffer.data: [i64]` (`dram.spl:30`) becomes a flat word arena of
`WRITE_BUFFER_CAP_BLOCKS * PAGE_WORDS` = 16 * 512 = **8192 words = 65536 bytes**,
which — not coincidentally — is exactly the already-declared
`WRITE_BUFFER_DRAM_BUDGET_BYTES = 65536` (`dram.spl:11`). The budget constant is
currently unenforced against the real arena; after widening it becomes a genuine
invariant: `data.len() * WORD_BYTES == WRITE_BUFFER_DRAM_BUDGET_BYTES`. Assert it
in `dram_write_buffer_new` (`dram.spl:41`).

`DramSpan` (`dram.spl:36`) already has `base`/`len`/`ok` and needs no shape
change — `base` becomes a word offset into the flat arena and `len` a word count,
so the existing `effective_cap` clamping logic (`dram.spl:45-56`) survives intact.

Slot accessors `dram.spl:146` (`me.data[slot] = byte & 0xFF`) and `dram.spl:164`
become span copies. The `& 0xFF` masking disappears — it is the byte-stand-in
tell.

### 1.4 PRP

`hil_command.spl:69-76` packs two payload bytes into `NvmeCmd.data` and calls it
PRP. Once `NvmeCmd` carries a real buffer reference, `prp_pack` is deleted and
replaced by a genuine PRP list: `prp1`, `prp2`, and a PRP-list page. **§6.1's P1
line item "PRP validation" is not implementable before this** — there is
presently nothing to validate. Record that dependency explicitly in the P1 gate.

### 1.5 Migration: bottom-up, one layer per commit

The tree is 73 files in `fw/` with per-layer `*_check.spl` gates. A single
flag-day commit would red every gate at once and be unreviewable. Instead widen
**bottom-up**, each commit keeping that layer's own check green, with a compat
shim carrying the layers above unchanged:

```
fn page_from_word(w: i64) -> PageData      # word -> word 0, rest zero
fn page_to_word(p: PageData) -> i64        # word 0
```

Every upper layer keeps compiling against `i64` by wrapping/unwrapping at the
boundary the commit has not yet reached. The shim is **debt with an owner**: the
final commit deletes both functions, and a grep for them is the completion test.

| # | Commit | Widens | Gate that must stay green |
|---|---|---|---|
| D1 | **LANDED 2026-09-01.** `nvme_payload.spl` + profile constants, no callers | new types only | new `payload_types_check.spl` — green |
| D2 | **LANDED 2026-09-01.** OOB fold, in BOTH behavioural backends | `fil_nand.spl` three arrays → `oob: [OobData]`; same fold in `fil_nand_device.spl` (`fil_nand_emu.spl` untouched — physics backend, own geometry) | `fil_nand.spl` selftest via `test_fw.spl`, `nd_types_check.spl` — green |
| D3 | **LANDED 2026-09-01.** NAND media stores real page bytes | `fil_nand.Nand.data:[i64]` → `page:[PageData]`; `fil_nand_device.page_data` + the ONFI `din`/`dout` latches → `PageData`. i64 seams (`program`/`read_page`/`corrupt_page_data`/`data_in`/`data_out`) preserved via the shim; page-wide `program_page`/`read_page_data`/`corrupt_page`/`data_in_page`/`data_out_page` added for D4/D5 | `fil_nand_emu_check.spl`, `fil_nand_emu_e2e_check.spl`, `nvme_emu_media_check.spl`, `test_fw.spl` — all green; cost recorded in `doc/08_tracking/bug/nvme_fw_payload_widening_d3_cost_and_silent_field_assign_2026-09-01.md` |
| D4 | ECC | `fil_ecc.spl:13,33,68,73,81,114` → `CodewordSpan` | `ecc_check.spl` — **unblocks workstream A** |
| D5 | FIL/FMC | `fil.spl:28,62,104,129,275`; `fil_fmc.spl:38,46,89` | `fil.spl:316+` selftest, `fil_fmc.spl:300` |
| D6 | RAIN | `rain.spl:32,37,53,59` — parity over pages | `rain_check.spl`, `rain_ftl_check.spl` |
| D7 | FTL | `ftl.spl:144,189,247` | `ftl_selftest`, `gc_safety_check.spl`, `durability_check.spl` |
| D8 | DRAM | `dram.spl:29-30,101,121,146,164` + budget assert | `dram_buffer_check.spl` |
| D9 | HIL + rings | `hil_command.spl:40,57-76`; `hil_queue.spl:98,161`; `hil.spl:45` | `hil_queue_backpressure_check.spl`, `queue_tail_backpressure_check.spl`, `host_transport_check.spl` |
| D10 | NVMe cmd/cpl | `nvme_types.spl:98,113`; `nvme_controller.spl:414,422,479` | `nvme_controller.spl`, `nvme_emu_media_check.spl`, `nvme_main.spl` |
| D11 | Shim removal + real PRP | delete `page_from_word`/`page_to_word`, `prp_pack` | full `test_fw.spl` |

Each commit updates only its own layer's expectation constants (the check-file
list in §0.1), so no commit touches more than ~8 files.

---

## 2. Command-set inventory and P0–P3 roadmap

### 2.1 What exists today

**I/O opcodes — 5** (`nvme_types.spl:14-18`):
`OP_FLUSH 0x00`, `OP_WRITE 0x01`, `OP_READ 0x02`, `OP_WRITE_ZERO 0x08`,
`OP_DSM_TRIM 0x09`.

**Admin opcodes — 13** (`nvme_admin_types.spl:14-26`):
`DELETE_SQ 0x00`, `CREATE_SQ 0x01`, `GET_LOG 0x02`, `DELETE_CQ 0x04`,
`CREATE_CQ 0x05`, `IDENTIFY 0x06`, `ABORT 0x08`, `SET_FEATURES 0x09`,
`GET_FEATURES 0x0A`, `ASYNC_EVENT 0x0C`, `FW_COMMIT 0x10`, `FW_DOWNLOAD 0x11`,
`FORMAT_NVM 0x80`.

**Identify CNS values — 2** (`nvme_admin_types.spl:32-33`): `CNS_NAMESPACE 0x00`,
`CNS_CONTROLLER 0x01`. No CNS 0x02 (active NS list), no 0x03 (NS descriptor).

**Status codes — 11**: `nvme_types.spl:21-27` (7) plus `nvme_admin_types.spl:51-54`
(4 queue-management codes).

### 2.2 Mapped onto §6.1

| Stage | §6.1 requirement | State | Gap |
|---|---|---|---|
| **P0** | Controller enable/disable/reset | partial | reset paths exist in `nvme_controller.spl`; no CC.EN/CSTS.RDY register model |
| P0 | Admin SQ/CQ | **present** | `nvme_admin_types.spl:62` `ADMIN_QID = 0` |
| P0 | Identify | **present but untruthful** | `nvme_admin.spl:105-123` hand-written; `lba_bytes: 4096` is false (§0). CNS 0x02/0x03 missing |
| P0 | Get Log Page minimum | partial | `ADMIN_GET_LOG` exists; SMART builder exists (`nvme_admin.spl:10`). **Error log (LID 0x01) entries not modelled** |
| P0 | Create/Delete I/O SQ/CQ | **present** | full set, with `SC_CQ_INVALID`/`SC_INVALID_QID`/`SC_INVALID_QSIZE`/`SC_QUEUE_BUSY` |
| P0 | Abort basics | **present** | `nvme_controller.spl:873` |
| **P1** | Read / Write / Flush | present, **1 word wide** | blocked on §1 |
| P1 | Write Zeroes, DSM — "if truly implemented" | present | must widen; today `WRITE_ZERO` zeroes a word |
| P1 | **PRP validation** | **absent** | `prp_pack` (`hil_command.spl:69`) is two packed bytes, not a PRP. **Hard-blocked on §1.4** |
| **P2** | Multiple queues | **present** | `MAX_IO_QUEUES`, `nvme_qset.spl` |
| P2 | MSI/MSI-X | absent | no interrupt model |
| P2 | Namespace lifecycle | absent | single fixed NS (`nvme_types.spl:94` `nsid` "single namespace model: 1") |
| P2 | Power-state / health | **present** | `power_thermal.spl`, `rel_health.spl`, AER (`nvme_controller.spl:901`) |
| P2 | Firmware slot/update | partial | `FW_COMMIT`/`FW_DOWNLOAD` opcodes declared; slot model absent |
| P2 | Telemetry | absent | no telemetry log pages |
| **P3** | SGL | absent | `hil_command.spl:2` mentions SGL in a docstring only |
| P3 | ZNS / KV / computational / SR-IOV / fabrics | absent | separately profiled modules, out of scope |

**Ordering.** D1–D11 (§1.5) precede P1 completion and P0's Identify truthfulness.
Nothing in P1 can be certified before D10.

---

## 3. Capability truthfulness

### 3.1 The state machine

Every capability (opcode, feature id, log page id, Identify bit) carries exactly
one state. This is the rule §5 and §6.1 both state, made mechanical:

| State | Meaning | Command behaviour | Identify/log bit |
|---|---|---|---|
| `NotCompiled` | code not built into this image | `SC_INVALID_OPCODE` | **0** |
| `CompiledUnsupportedOnProfile` | code exists, profile disables it (e.g. ZNS in a conventional profile) | `SC_INVALID_OPCODE` | **0** |
| `SupportedUncertified` | implemented, but its five test obligations (§4) have not all passed | `SC_INVALID_OPCODE` — **never a silent no-op** | **0** |
| `SupportedCertified` | all five obligations pass, recorded | normal execution | **1** |

The load-bearing transition is `SupportedUncertified` → `SupportedCertified`.
Only that edge may set a bit. `SupportedUncertified` deliberately behaves
identically to `NotCompiled` *at the host interface* — this is what makes the
rule enforceable rather than aspirational, and it means a half-finished feature
cannot leak into a host's view by accident.

`Identify.lba_bytes` is not a bit but the same rule applies to fields: a field
value must be derived from the certified profile, never typed by hand.

### 3.2 Certification records drive generation

Add `fw/nvme_capabilities.sdn` — one record per capability:

```
capability:
  id: OP_WRITE_ZERO
  kind: io_opcode
  state: SupportedUncertified
  advertises: { identify: oncs.write_zeroes, bit: 3 }
  obligations:
    positive:    fw/nvme_controller.spl::write_zero_io_clears
    negative:    fw/nvme_controller.spl::write_zero_rejects_nonzero_data
    reset:       fw/nvme_main.spl::write_zero_survives_reset
    fault:       fw/durability_check.spl::write_zero_prog_fail
    persistence: fw/nvme_main.spl::write_zero_survives_power_cycle
  certified_by: <check-run id, or empty>
```

A generator (`nvme_capgen`, run as part of the build) reads this file and emits
`fw/nvme_identify_generated.spl`, replacing the hand-written builders at
`nvme_admin.spl:105-123`. Two rules make it fail-closed:

1. **A record whose `state` is not `SupportedCertified` emits a 0 bit.** There is
   no override flag. `certified_by` is written only by the check runner, never by
   hand.
2. **Every advertised field must trace to a record.** `lba_bytes` is emitted from
   the profile constant `LBA_BYTES` (§1.1), and the generator asserts
   `LBA_BYTES == PAGE_BYTES * LBAS_PER_PAGE` and that the media array width
   matches. Under today's tree that assertion **fails**, which is the correct
   outcome and the direct fix for `nvme_admin.spl:109`.

A gate script (`scripts/check/check-nvme-capability-truthfulness.shs`) then
enforces, fail-closed, following this repo's guard conventions (verdict as the
last stdout line; `PASS — <n> capability(ies) checked, 0 unbacked` / `FAIL` /
`ERROR — nothing was checked` on a zero-capability scan, with a fatal
`--selftest`):

- no Identify/log bit set in the generated file lacks a `SupportedCertified` record;
- no capability record names an obligation test that does not exist;
- no capability marked `SupportedCertified` has a failing or missing obligation;
- the generated file is byte-identical to a fresh generation (no hand edits);
- `nvme_admin.spl` contains no literal numeric Identify field (grep ratchet), so
  a hand-written `lba_bytes: 4096` cannot reappear.

Initial run will be honestly RED — every current capability is at best
`SupportedUncertified`. Land it advisory, promote to mandatory when green, per
the precedent of `check-stage-binaries-runnable.shs` in `.claude/rules/vcs.md`.

---

## 4. Per-stage test obligations

Five obligations per capability. All five must pass before certification; four
of five is `SupportedUncertified`.

| Obligation | Question it answers | Example (against existing tests) |
|---|---|---|
| **Positive** | does it do the thing? | `nvme_controller.spl:687` "IO read returns written byte" — after D10 this becomes *page* comparison, not byte |
| **Negative** | is a malformed/illegal request **rejected with the right status**, not silently accepted? | `nvme_controller.spl:734` "oversized IO write leaves first LBA untouched"; `hil_command.spl:57-61` non-zero-`data` rejections |
| **Reset** | does controller reset / queue delete leave it consistent, with no stale in-flight state? | `qset_delete_check.spl`, `task_pool_fail_closed_check.spl` |
| **Fault** | under injected media/program/ECC failure, does it fail *correctly* (`SC_MEDIA_ERR`, block retire) rather than return wrong data? | `fil.spl:333`, `fil_nand_device.spl:401`, `ecc_check.spl:20,31` |
| **Persistence** | does the effect survive a power cycle via the journal? | `nvme_main.spl:165-166` "LBA 200 survives power cycle"; `firmware.spl:273` |

### Per-stage gating

| Stage | Obligation set that gates it |
|---|---|
| D1–D11 | each commit's layer check stays green; **D4 additionally requires a fault obligation over a full `CodewordSpan`** — multi-bit errors inside one codeword, correctable and uncorrectable, which is impossible today (`fil_ecc.spl:33` is one word) |
| P0 | all five for: reset, admin queue create/delete, Identify (incl. the `LBA_BYTES` consistency assertion), Get Log error log, Abort |
| P1 | all five for Read/Write/Flush **at full page width**, plus a dedicated negative set for PRP validation (misaligned PRP, PRP crossing a page boundary, PRP list overrun, null PRP) — none of which can even be written before §1.4 |
| P2 | all five per queue for multi-queue; fault + persistence for firmware slot commit; reset for namespace attach/detach |
| P3 | full set per separately profiled module; no P3 capability may be `SupportedCertified` while any P1 capability is not |

### Anti-regression

Per this repo's memory rule *"fixes need reproduce + similar tests"*: the
widening commits D3, D4 and D10 must each ship a spec that **fails before the
commit** — specifically, one asserting that a page write of two differing words
reads back both words. Today that assertion cannot pass, and that is the
one-line proof that §0 is real.

---

## 5. Dependencies out

- **Workstream A (ECC offload)** consumes `CodewordSpan` from D4. It cannot be
  specified before then: an offload engine over a single `i64` has no buffer,
  no DMA descriptor, and no latency worth measuring.
- **Workstream G4** likewise waits on D4.
- Any DIF/PI work waits on `MetadataLayout` (D2) and is P3.
