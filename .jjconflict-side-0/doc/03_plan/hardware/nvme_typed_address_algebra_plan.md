# Typed Address Algebra for the NVMe Firmware — Workstream I

**Parent:** `doc/03_plan/hardware/nvme_complete_fw_mdsoc_offload_master_plan.md` §11.4 (workstream I)
**Scope:** design only. No source file is edited by this document.
**Date:** 2026-09-01
**Sibling workstreams referenced:** A (`nvme_offload_hw_sw_partition_design.md`), C (`nvme_controller_profile_portability_plan.md`), D (`nvme_command_set_and_payload_completeness_plan.md`), G (`simple_hardware_ir_single_source_plan.md`), J (address site census — **does not exist yet**, see §1.0).

**Requirement being served (user, verbatim intent):** every address value must be a hard type, not a bare `i64` — channel, bank, CE, CE-ready, way, LUN, plane, block, wordline, page, string, layer, sector, LBA, PPN, VPN, band, queue-slot, PRP entry. The same name means a different format at different layers, so a **namespace per layer** is mandatory. Naming convention: role suffix (`_lba`, `_ppn`, `_ch`, `_wl`, `_blk`), layer-based namespacing.

Everything under **MEASURED** was executed or read in this session, with `file:line`. Everything under **PROPOSED** is design. Inferences are marked *(inferred)*.

---

## 0. Executive summary — the decisive finding first

**Simple provides no compile-time nominal safety for address types today, by any mechanism, because argument type checking itself does not run on any path tested.** This is not a property of `newtype` versus structs; it is more fundamental. Measured, this session, on `bin/simple` = `bin/release/x86_64-unknown-linux-gnu/simple` (the Rust seed; `--version` = `Simple Language v1.0.0-RC` and it self-identifies as a bootstrap seed):

| Probe | Expected if types enforced | **Measured** |
|---|---|---|
| `takes_i(x: i64)` called with `"hello"` | type error | **runs**, prints `t=5557897342433` (a raw pointer) |
| `takes_lba(x: Lba)` called with a `Ppn` (both `newtype … = i64`) | type error | **runs**, prints `cross_ok=7` |
| `takes_lba(x: Lba)` called with bare `5` | type error | **runs**, prints `bare_ok` |
| `takes_blk(b: NdBlock)` called with `NdPage(idx: 3)` (single-field structs) | type error | **runs**, prints `struct_cross=3` |
| `bin/simple lint` on all of the above | at least one finding | **`Lint passed: all files clean`** |
| `SIMPLE_JIT_STRICT=1 bin/simple run` on the struct and `text`→`i64` cases | hard error | **runs clean** |

**Therefore:** a wrapper type in this codebase is *documentation and a grep target*, not a guarantee. The `emu/nvme_ct.spl:7-13` header already says this in prose ("newtypes are NOT enforced for argument passing"); this session extends the finding to single-field structs, to `newunit`, to lint, and to `SIMPLE_JIT_STRICT` — i.e. to everything.

**Consequence, stated in the master plan's own §2-correction idiom:** compiler work (a nominal argument-type check) is **on the critical path** for enforcement of this workstream, not adjacent to it. Until it lands, enforcement of the typed-address discipline must come from a **fail-closed textual gate** (§6), which is the same substitute workstream B adopted for the missing `call(...)` pointcut. Per CLAUDE.md ("fix it or record a concrete bug/feature request instead of silently normalizing the workaround"), §7 files that request concretely.

Second decisive finding, and the reason `newunit` must be **rejected outright**: it does not merely fail to enforce, it *silently rewrites the value*. See §2.2.

---

## 1. MEASURED — census of the current truth

### 1.0 Scope and its boundaries

`examples/09_embedded/simpleos_nvme_fw/` holds **287** `.spl` files in total, of which **`fw/` holds exactly 72** — the 72 the brief names. `emu/` (10 files) and `fw_rv32/` (≈205 files) are **separate coordinate universes** with their own geometry and are **out of conversion scope**; §3 gives them namespaces so the distinction is nameable, but they are not migrated by §5.

**Workstream J's report does not exist.** `ls doc/09_report/ | grep -i census` returns only `dangling_import_census_2026-08-18.md`, `showcase_matrix_census_2026-07-30.md`, `skipped_flaky_test_census_2026-08-21.md`. The census below is therefore **representative, not exhaustive** — it establishes the coordinate spaces, the collisions, and a mechanical count. The per-site worklist remains J's deliverable, and §5's gate baseline must be regenerated against it when it lands.

### 1.1 The mechanical count

A grep for function/method parameters whose name is address-shaped and whose declared type is bare `i64`:

```
grep -n -E '(fn|me) [a-z_]+\(.*\b(lba|ppn|blk|block|page|ch|channel|way|plane|band|slot|addr|qid|cid|nsid|index)[a-z_]*: i64' fw/*.spl
```

**202 such parameter sites across `fw/`.** Distribution (top files):

| File | sites | File | sites |
|---|---|---|---|
| `ftl.spl` | 33 | `fil_nand.spl` | 12 |
| `nvme_admin.spl` | 19 | `nvme_types.spl` | 9 |
| `nvme_qset.spl` | 18 | `ftl_map.spl` | 7 |
| `fil.spl` | 18 | `hooks.spl` | 6 |
| `ftl_band.spl` | 14 | `rain.spl` | 5 |
| `fil_nand_device.spl` | 14 | `nvme_controller.spl` | 5 |
| `fil_fmc.spl` | 14 | `fil_scheduler.spl` | 4 |
| `fil_nand_emu.spl` | 13 | `fil_ecc.spl` | 3 |

This 202 is the number §6's completion gate ratchets to zero. It is a *lower* bound on the work: it counts parameters only, not struct fields, return types, array element types, or locals.

### 1.2 Which coordinates exist, and where

**Geometry constants** — `fw/nvme_types.spl:43-49`: `NUM_PLANES=4`, `BLOCKS_PER_PLANE=16`, `PAGES_PER_BLOCK=64`, `NUM_BLOCKS=64`, `NUM_PAGES=4096`, `LBA_COUNT=3072`. `NUM_CHANNELS=8` lives elsewhere, at `fw/fil_scheduler.spl:21`.

**The canonical address helpers** — `fw/nvme_types.spl:122-137`:

```
fn ppn_block(ppn: i64) -> i64:      ppn / PAGES_PER_BLOCK
fn ppn_page(ppn: i64) -> i64:       ppn % PAGES_PER_BLOCK
fn block_first_ppn(blk: i64) -> i64: blk * PAGES_PER_BLOCK
fn ppn_in_range(ppn: i64) -> bool:  ppn >= 0 and ppn < NUM_PAGES
fn block_in_range(blk: i64) -> bool: blk >= 0 and blk < NUM_BLOCKS
```

Every one is `i64 -> i64`. Nothing distinguishes an argument that is a block from one that is a page.

**Coordinate inventory by layer, with production/consumption sites:**

| Coordinate | Produced at | Consumed at | Type today |
|---|---|---|---|
| host LBA | `NvmeCmd.lba` (`nvme_types.spl:92-98`), `cmd_make` (:100) | `ftl_map.lookup/update` (`ftl_map.spl:125,156`), `ftl_map_lba_valid` (:67) | `i64` |
| CID / QID / NSID | `cmd_make_nsid` (`nvme_types.spl:103`), `hil_queue.spl:82,104` | `cid_valid` (`nvme_types.spl:106`) | `i64` |
| PRP entry | `prp_pack(first_base, second_base)` (`hil_command.spl:69`), `prp_first_base`/`prp_second_base` (:72,75) | `prp_byte` (:78), `host_write_byte` (:87) | `i64` (**two addresses folded into one**) |
| DRAM span / index | `dram.spl:36` `DramSpan`, `alloc` (:82), `stage(span,index,byte)` (:125) | `byte(span,index)` (:149) | `i64` |
| FTL logical page (== LBA today) | `ftl.spl` map path | `ftl.spl:288,582` | `i64` |
| PPN (flat) | `block_first_ppn`, `ftl_band.alloc_page` (`ftl_band.spl:93`) | `fil.program/read` (`fil.spl:104,122`), `ftl_band.mark_valid/is_valid` (:143,175) | `i64` |
| band / block | `ftl_band.spl:49,164,181,188,260` | `ftl_gc`, `rel_wear` | `i64` |
| RAIN group / stripe / channel | `rain_blk(group,channel)` (`rain.spl:83`), `rain_ppn(group,channel,page)` (:89), `rain_stripe_idx(ppn)` (:95) | `rain.data_at(ch)` (:40), `reconstruct(failed_ch)` (:48) | `i64` |
| FIL channel | `channel_of(blk) = blk % NUM_CHANNELS` (`fil_scheduler.spl:25-28`) | `channel_ready(ch)`, `queue_depth(ch)` (:55,69) | `i64` |
| NAND block/page (device) | `fil_nand.spl:82,115` re-deriving via `ppn_block`/`block_first_ppn` | `nand.read_page(ppn)` (:241) | `i64` |
| way / bank(LUN) / plane / wordline | **declared but inert** — `nd_types.spl:53-65`, defaulted to index 0 by `nd_addr_of_ppn` (:127-136) | — | `Nd*` structs |
| CE / CE-ready / string / layer / sector / VPN | **do not exist anywhere in `fw/`** | — | — |

*(inferred)* "FTL logical page" is not a distinct concept in this firmware: the L2P is indexed directly by host LBA (`ftl_map.spl:117,125`), so host-LBA and FTL-logical-page are currently the *same* space. That is a design fact worth preserving deliberately rather than by accident — §3 gives them separate types precisely so a future 4K-vs-512B host block size cannot silently alias them.

### 1.3 Prior art already in the tree: `nd_types.spl`

`fw/nd_types.spl` is a **partial, already-landed implementation of this workstream**, and this plan must extend rather than contradict it. It defines seven single-field structs — `NdChannel`, `NdWay`, `NdBank`, `NdPlane`, `NdBlock`, `NdWordline`, `NdPage` (`:53-65`) — a composed `NdAddr` (`:67-73`), free-function constructors (`:76-97`), and `nd_addr_of_ppn` / `nd_ppn_of` converters. Its contract is `doc/01_research/hardware/nand_recovery/typed_nand_addressing_local.md` §4, which is the **adjudicated prior decision on exactly this topic**. Its standing rulings, which this plan adopts:

- **Peer-leaf placement**, not a fourth layer (research §4.2): `nd_types.spl` imports only `nvme_types.*`, at the same depth as `nvme_types`/`rel_types`, so `fil`, `ftl`, and every `rel_*` can import it without a cycle.
- **Field name `idx`**, not `val` (a keyword) and not `payload` (the crypto `ctypes.spl` convention).
- **No fake math.** `way`/`bank`/`plane` are declared with `NdAddr` slots but get no conversion formula; `nd_addr_of_ppn` leaves them at 0 and `nd_types_check.spl:120,122` asserts exactly that ("honest, not faked").
- **`NdWordline` is a distinct type from `NdPage`** even though they are numerically identical under v1 SLC, precisely so the v2 MLC/TLC upgrade (2-3 pages per wordline) cannot silently corrupt a wordline-keyed policy (`nd_types.spl:139-149`, research §3).

Live consumers exist: `rel_vref.spl:89,97,107` take `blk: NdBlock`; `fil.spl:169,203` likewise; `rel_ladder_check.spl:83,176` construct `NdBlock`.

### 1.4 THE HIGHEST-VALUE OUTPUT — coordinate spaces that are silently interchangeable

Each row is a pair of *different* coordinate spaces that share one type today, so a transposition compiles, runs, and produces a wrong address.

**C1 — `UNMAP` = `NO_PPN` = `NULL_IDX` = `-1`, three declared domains, one value.**
`nvme_types.spl:30-40` documents an "Index-handle law" carving out three vocabularies — L2P/ppn, ppn-return, and generic handle/index — and then assigns all three the literal `-1`, noting `NULL_IDX` is "kept a literal, not a val-to-val alias". The comment is an admission: the law is a *naming* convention with no type behind it. A pool handle compared against `UNMAP`, or an unmapped L2P entry passed where a null queue index is expected, is indistinguishable to the compiler. `ftl.spl` alone has ~40 `UNMAP` comparison sites (`:169,193,211,251,258,288,309,375,533,565,589,634,637,643,647,659,672,683,689,726,729,736,741,744,745,758,767,792,799,800,803,829,843,981,998,1009,1021,1032,1081`). **This is the single largest interchangeability hazard in the tree.**

**C2 — block-index and page-index are the same type, and both flow through `ppn_block`/`block_first_ppn`.**
`ppn_block(ppn: i64) -> i64` and `block_first_ppn(blk: i64) -> i64` (`nvme_types.spl:122,128`) are mutually inverse-ish but structurally identical in signature. `block_first_ppn(ppn_block(x))` typechecks; so does the wrong composition `ppn_block(block_first_ppn(x))` — and so does `ppn_block(blk)`, which is meaningless but silent. `fil_nand.spl:82,115` re-derives both.

**C3 — FTL block and NAND-device block share a type across the layer boundary.**
`ftl_band.free_block(blk: i64)` / `set_bad(blk: i64)` (`ftl_band.spl:188,260`) and `fil.erase(blk: i64)` / `block_bad(blk: i64)` (`fil.spl:221,242`) are the FTL-side and FIL-side halves of the same coordinate — but nothing enforces that they *stay* the same. This is exactly the "a block at the FTL layer is not a block at the NAND device layer" case the brief names; today they are the same only by convention.

**C4 — `rain.spl`'s channel and `fil_scheduler.spl`'s channel are two independently-derived spaces with one type.**
`rain_blk(group, channel) = group*NUM_CHANNELS + channel` (`rain.spl:83`) and `channel_of(blk) = blk % NUM_CHANNELS` (`fil_scheduler.spl:28`) agree today. `nd_types.spl:110` duplicates the constant a *third* time as `ND_NUM_CHANNELS: i64 = 8` with an explicit comment that the check file is the only anti-drift guard. Three definitions, one type, no compiler-visible link.

**C5 — same signature, two types for the same concept, inside one `impl`.**
`fil.spl:203` `me decay_vref_on_erase(blk: NdBlock)` sits eight lines from `fil.spl:208` `me calibrated_offset(blk: i64)`. `fil.spl:169` is `me read_with_ladder(ppn: i64, blk: NdBlock)` — **one typed and one bare parameter in the same signature**. The migration is genuinely half-done and currently *inconsistent*, which is worse for a reader than uniformly bare.

**C6 — `prp_pack` folds two host addresses into one `i64`.**
`hil_command.spl:69` `prp_pack(first_base: i64, second_base: i64) -> i64`. The result is a single scalar carrying two distinct PRP entries, unpacked at `:72,75`. There is no type distinguishing the packed form from either component, so a packed value can be passed anywhere a base address is accepted.

**C7 — `fw/` PPN and `emu/` PPN are different formats with the same name.**
`fw/nvme_types.spl:122-131`: flat, `ppn = blk*64 + page`, **no channel dimension at all** (channel is a derived view, C4). `emu/nvme_ct.spl:60`: five-dimensional packed, `ppn = ((((ch*2+bank)*2+plane)*2+block)*8+page)`, over a 2×2×2×2×8=128-page geometry. Both are called "ppn"; both are `i64` in `fw/` and `Ppn` in `emu/`. Anything that moves a value between the two universes — a capture harness, a differential oracle — is a silent-corruption site. This is the brief's "same name, different format at different layers" in its purest measured form, and it is the reason §3's namespacing is mandatory rather than cosmetic.

**C8 — `openssd_config.spl` geometry fields are `i64` and unbound to the address types.**
`openssd_config.spl:28-32`: `channels`, `ways_per_channel`, `blocks`, `pages_per_block`, `lbas`, all bare `i64`, all per-profile (2/8/1 channels; 8/1 ways; 64/2 blocks; 64/1 pages). The RV32 profiles declare `blocks: 2, pages_per_block: 1` while `fw/`'s address math uses the compile-time constants `NUM_BLOCKS=64`, `PAGES_PER_BLOCK=64` unconditionally. *(inferred)* the profile geometry is therefore **descriptive only** — it does not reach the address helpers — which is precisely the gap workstream C must close and §4.2 depends on.

---

## 2. MEASURED — what wrapper mechanisms Simple actually supports

### 2.1 `newtype` — exists, does not enforce

The keyword is real: `TOK_KW_NEWTYPE = 198` (`src/compiler/10.frontend/core/tokens.spl:167,332,416`), parsed at `src/compiler_rust/parser/src/stmt_parsing/var_decl.rs:1279-1281` and `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:1468-1514`, which lowers `newtype Meters = i64` to "wrapper struct with single 'value' field". It has a landed spec — `test/01_unit/compiler/newtype_ops_spec.spl` — documenting auto-derived `__add__`/`__sub__`/`__mul__`/`__div__`/`__eq__`/`__lt__`/`__gt__` for numeric wrappers.

**Note a live documentation defect:** `src/compiler/35.semantics/lint/primitive_classification.spl:86` asserts *"`newunit` is the actual keyword (`newunit Name: T`); `newtype` does not exist."* That is contradicted by the tokens table, both parsers, the landed spec, and this session's execution. Recorded here; §7 files it.

Measured (`newtype Lba = i64`, `newtype Ppn = i64`): `takes_lba(p: Ppn)` → runs, `cross_ok=7`. `takes_lba(5)` → runs, `bare_ok`. Zero diagnostics from `run`, `lint`, or `SIMPLE_JIT_STRICT=1`.

Two further costs, both measured or cited rather than assumed:
- **Auto-derived arithmetic is the wrong algebra for addresses.** `Width + Width -> Width` (`newtype_ops_spec.spl`) is right for a quantity and wrong for a coordinate: `Lba + Lba` and `Ppn * Ppn` are meaningless, and a newtype hands them to you for free.
- **Importing a newtype forces JIT→interpreter demotion.** `emu/nvme_memcpy.spl:8,55` records that importing `nvme_ct`'s `Ppn` newtype "forces a JIT→interpreter" fall back — a measured performance penalty the module comments around.

### 2.2 `newunit` — exists, does not enforce, and **silently scales the value**

`newunit Name: T as suffix` is real and registry-backed: parsed at `enum_module_body.spl:1442-1459` calling `newunit_register`, recorded at `10.frontend/core/types.spl:858-868`, collected into the compile-start unit registry at `30.types/units/unit_registry.spl:260-287`, with a system spec at `test/03_system/app/compiler/feature/world_units_newunit_spec.spl` asserting nominal 1:1 wrappers carry an identity base factor.

Measured, with `newunit LbaU: i64 as lbau` and `newunit PpnU: i64 as ppnu`:

```
val p: PpnU = 7
takes_lba(p)   ->  cross=56      # not 7
takes_lba(5)   ->  bare=40       # not 5
```

**Both results are multiplied by 8** — exactly `<< 3`. No error, no warning; the value is silently rewritten. *(inferred, two candidate causes, not distinguished by this probe)*: either (a) a unit-conversion factor is applied on a cross-unit assignment that should have been rejected outright, or (b) a 3-bit tagged-value representation is leaking through the wrapper — the shift-by-3 is equally consistent with a tag being left in place. **Either way it violates `newunit`'s own landed contract:** `test/03_system/app/compiler/feature/world_units_newunit_spec.spl` (REQ-WUN-001) asserts that a `newunit` declaration is recorded as a *nominal 1:1 wrapper* carrying "an identity base factor (1/1)" — `base_factor.numerator == 1`, `base_factor.denominator == 1`. A factor of 8 is a measured violation of that spec, not merely surprising behaviour. The behaviour is disqualifying: **`newunit` must not be used for addresses.** A wrapper that fails to enforce is merely useless; one that quietly returns `8*ppn` where you asked for `ppn` is an active corruption source in an SSD firmware. §7 files this as a bug.

### 2.3 Single-field structs — no enforcement either

Measured: `takes_blk(b: NdBlock)` called with `NdPage(idx: 3)` runs and returns `3`, under both the default path and `SIMPLE_JIT_STRICT=1`. Structural, not nominal.

### 2.4 Type aliases, private fields, refinement

- **Type aliases** exist (`parse_type_alias`, `var_decl.rs:729-748`; `Node::TypeAlias`, `ast/nodes/core.rs:27`). An alias of `i64` is by definition assignable from any `i64`. **Aliases give zero safety** and are excluded.
- **Field visibility** exists in the AST (`Visibility::Private`, `ast/enums.rs:37,50`; `visibility` on every definition node). Whether *cross-module* private-field access is actually rejected was **not tested** and, given §0, would be surprising. **This design must not depend on private fields** — treated as unverified and assumed unavailable, per the hardening plan §9.3 warning quoted below.
- **Refinement types / bounded integer types:** no evidence found. Assumed absent.

### 2.5 The binding constraint from the hardening plan

`nvme_ssd_firmware_hardening_design_plan.md` §9.3 (~line 839):

> Avoid a design where every wrapper still contains unrestricted `i64` and every call can construct it directly. Constructors must be private or validated, and generated constants should create compile-time values.

Since privacy is unverified (§2.4) and nominal typing is absent (§0), **"validated" is the only half of that sentence this design can currently honour**, and it must be honoured at *runtime* by the constructor plus at *review time* by the gate. §7 records the shortfall rather than papering over it.

---

## 3. PROPOSED — the type algebra

### 3.1 Choice of mechanism: extend `nd_types.spl`'s single-field struct pattern

Since **no mechanism enforces**, the choice is made on the secondary grounds, all of which point the same way:

| Criterion | single-field struct | `newtype` | `newunit` |
|---|---|---|---|
| enforcement today | none | none | none |
| silent value corruption | no | no | **yes, ×8 (§2.2)** |
| unwanted auto-derived arithmetic | no | yes | yes |
| JIT demotion on import | not observed | **yes** (`nvme_memcpy.spl:8`) | not tested |
| live consumers in `fw/` already | **yes** (`fil.spl:169,203`, `rel_vref.spl:89`) | no (only `emu/`) | no |
| adjudicated by a landed research contract | **yes** (`typed_nand_addressing_local.md` §4) | no | no |

**Decision: every address type is a single-field struct with field `idx: i64` (v1) → `idx: u32` (v2, §4.4), constructed only through a validated free function.** This extends `nd_types.spl` rather than competing with it.

### 3.2 Layer namespaces

Namespacing is by **type-name prefix**, because Simple's module system is flat-import (`use nvme_types.*`) and a prefix is what a reader and a grep both see. Five namespaces:

| Prefix | Layer | Module (proposed) | Existing anchor |
|---|---|---|---|
| `Hst` | HOST — PCIe/NVMe transport, queues, PRP, DMA | `fw/host_addr.spl` | `hil_command.spl`, `hil_queue.spl`, `nvme_types.spl` |
| `Ftl` | FTL — mapping, bands, journal, GC | `fw/ftl_addr.spl` | `ftl_map.spl`, `ftl_band.spl` |
| `Fil` | FIL — scheduler, channel/way arbitration, ECC framing | `fw/fil_addr.spl` | `fil.spl`, `fil_scheduler.spl` |
| `Nd` | NAND device — chip-internal physical coordinates | `fw/nd_types.spl` (**exists**) | `nd_types.spl:53-65` |
| `Emu` | emulator universe (`emu/`), **out of migration scope** | `emu/nvme_ct.spl` (exists) | `nvme_ct.spl:48-57` |

Prefixes already reserved and not to be reused: `Ne` (`nand_emu` chip-internal geometry) and `Rel` (reliability engine) — per `nd_types.spl:9-11`.

The `fw_rv32/` tree is a sixth universe; it is out of scope and this plan does not name types for it.

### 3.3 The types

**HOST (`Hst`)** — everything the host names; no media coordinate is visible here.

| Type | Wraps | Role suffix in variables |
|---|---|---|
| `HstLba` | host logical block address | `_lba` |
| `HstNsid` | namespace id | `_nsid` |
| `HstCid` | command id | `_cid` |
| `HstQid` | queue id | `_qid` |
| `HstQSlot` | slot index within a queue (SQ or CQ ring position) | `_qslot` |
| `HstPrpEntry` | one PRP entry (a host DMA base) | `_prp` |
| `HstPrpPair` | the packed two-entry form (`prp_pack`, C6) | `_prppair` |
| `HstSector` | sector within a logical block (D's payload widening) | `_sec` |
| `HstDramOff` | DRAM staging-buffer word offset | `_doff` |

**FTL (`Ftl`)** — logical-to-physical mapping; no host PRP and no NAND channel visible.

| Type | Wraps | Suffix |
|---|---|---|
| `FtlVpn` | FTL *virtual* page number — the L2P key | `_vpn` |
| `FtlPpn` | FTL flat physical page number (the L2P value) | `_ppn` |
| `FtlBlk` | FTL erase-block index | `_blk` |
| `FtlBand` | band index (allocation group) | `_band` |
| `FtlStripe` | RAIN stripe index | `_stripe` |
| `FtlGroup` | RAIN parity group | `_grp` |

`FtlVpn` and `HstLba` are numerically identical today (§1.2) and are still two types, for the same reason `NdWordline` and `NdPage` are (`nd_types.spl:139-149`): the identity is a v1 accident, not a law.

**FIL (`Fil`)** — the scheduler's view of parallelism.

| Type | Wraps | Suffix |
|---|---|---|
| `FilCh` | channel a request is dispatched on | `_ch` |
| `FilWay` | way / CE within a channel | `_way` |
| `FilCeReady` | CE-ready status index (per-CE ready line) | `_ceready` |
| `FilQDepth` | per-channel queue depth (a count, not an address — included only so it cannot be confused with `FilCh`) | `_qd` |

**NAND device (`Nd`)** — already landed; extended only where a consumer appears.

Landed: `NdChannel`, `NdWay`, `NdBank`, `NdPlane`, `NdBlock`, `NdWordline`, `NdPage`, `NdAddr` (`nd_types.spl:53-73`).
Specified-not-landed, per the no-unused-code law, until a real consumer exists: `NdString`, `NdLayer` (3D-NAND string/layer, needed by a LaVAR-class policy — research §3 names this as the v2+ consumer), `NdSector` (sub-page sector, arrives with D's 4096-byte payload).

`FilCh` and `NdChannel` are **deliberately two types.** `FilCh` is a scheduling lane; `NdChannel` is a physical bus. They coincide today (C4) and the conversion between them is an explicit function (§3.5), which is exactly the point where the three-way `NUM_CHANNELS` duplication becomes visible instead of silent.

### 3.4 Construction — validated, single-entry

Every type gets exactly **three** construction paths and no other:

```
# 1. Validated — the default. Returns an option; out-of-range is not representable.
fn ftl_blk_checked(raw: i64, g: FtlGeometry) -> Option<FtlBlk>

# 2. Clamping — for paths that must fail closed rather than propagate an option.
fn ftl_blk_or_none(raw: i64, g: FtlGeometry) -> FtlBlkOpt      # see §3.6

# 3. Trusted — for a value already proven in range by a prior check, named so
#    it is greppable and reviewable. NOT a general escape hatch.
fn ftl_blk_trusted(raw: i64) -> FtlBlk
```

The naming is the enforcement mechanism, given §0: `*_trusted` is a single grep, and §6's gate caps its call-site count with a ratcheted baseline exactly as `check-no-direct-rt.shs` caps direct `rt_*` calls. Range bounds come from a profile value (`FtlGeometry`), never from a global constant — §4.2.

The bare struct literal `FtlBlk(idx: n)` is **forbidden outside the constructor module** and is a gate-detected violation. This is the honest substitute for private fields (§2.4).

### 3.5 Inter-layer conversion — explicit, named, testable

No implicit coercion exists and none is proposed. Every layer crossing is a named function that can be traced, range-checked, and fault-injected. The full ladder:

```
HstLba   --host_lba_to_vpn(g)-->        FtlVpn
FtlVpn   --ftl_map_lookup(map)-->       FtlPpnOpt        # the L2P; may be unmapped
FtlPpn   --ftl_ppn_block()-->           FtlBlk
FtlBlk   --ftl_blk_to_nd(g)-->          NdBlock
FtlPpn   --ftl_ppn_to_nd_addr(g)-->     NdAddr           # the full decomposition
FtlBlk   --ftl_blk_to_fil_ch(g)-->      FilCh            # today: idx % channels (C4)
FilCh    --fil_ch_to_nd_channel()-->    NdChannel        # today: identity, still explicit
NdAddr   --nd_addr_to_ppn(g)-->         FtlPpn           # the inverse
HstPrpPair --prp_first()/prp_second()--> HstPrpEntry     # unpacks C6
```

**Naming rule:** `<srcns>_<srcrole>_to_<dstns>_<dstrole>`, lowercase, geometry passed explicitly. A conversion that is the identity function today is *still written as a function* — `fil_ch_to_nd_channel` — because that is the seam where the three `NUM_CHANNELS` definitions (C4) get reconciled to one, and the place a future non-identity mapping lands without a caller edit.

**Every conversion is total or option-returning; none traps.** A conversion that cannot produce a valid result returns the `*Opt` form (§3.6), never a sentinel.

### 3.6 Sentinels — `UNMAP` is deleted, not typed

C1 is the biggest hazard in the census, and a sentinel *inside* a typed address is a trap: it makes `-1` a legal `FtlPpn`, so every consumer must still remember to check, and the type buys nothing. Worse, under §4.4's u32 migration `-1` does not fit at all.

**Proposal: model absence as a distinct type, per the master plan's own preference for making the invalid state unrepresentable.**

```
struct FtlPpnOpt:                 # "a ppn, or nothing"
    present: bool
    ppn: FtlPpn                   # meaningless unless present

fn ftl_ppn_some(p: FtlPpn) -> FtlPpnOpt
fn ftl_ppn_none() -> FtlPpnOpt
fn ftl_ppn_is_mapped(o: FtlPpnOpt) -> bool
fn ftl_ppn_or(o: FtlPpnOpt, fallback: FtlPpn) -> FtlPpn
```

An `Opt` companion is generated for exactly the types that need one — measured from the census, that is `FtlPpn` (L2P entries, `ftl.spl` ~40 sites), `FtlBlk` (allocator/GC "no victim" returns, `ftl.spl:673,727,745`), and the pool/queue handle domain (`NULL_IDX`).

This **splits C1's three vocabularies into three types**: `FtlPpnOpt.none()` for the L2P domain, `FtlBlkOpt.none()` for block allocation, and a separate handle-option type for `NULL_IDX`'s pool/queue domain. `UNMAP`, `NO_PPN` and `NULL_IDX` (`nvme_types.spl:38-40`) are then **deleted**, not aliased — the "Index-handle law" comment block at `:30-40` becomes obsolete and is replaced by the type distinction it was trying to describe in prose.

*(inferred)* Whether Simple's `Option<T>` (used at `unit_registry` call sites and in `ftl.spl`'s match arms) is a better vehicle than a hand-rolled two-field struct depends on whether `Option<FtlPpn>` survives the fixed-width lowering in §4.4; the hand-rolled form is proposed because it is plainly a two-field POD and therefore certain to. This should be re-decided when §4.4's u32 migration is measured.

### 3.7 Packed ↔ structured, and the round-trip law

Both geometries in the tree are all powers of two — `fw/`: 64 blocks × 64 pages; `emu/`: 2·2·2·2·8 — so the codec should be **bit-packed with power-of-two field widths derived from the profile**, not the current `/` and `%`:

```
FtlPpn.idx  =  (blk << PAGE_BITS) | page              # v1 fw geometry, PAGE_BITS = 6
NdAddr      =  ch:CH_BITS | way:WAY_BITS | bank | plane | blk | page
```

This is not cosmetic — see §4.1: `shl`/`shr`/`and`/`or` are the *only* binops HWIR's strict lowering accepts today, while `/` and `%` are not accepted at all.

**The round-trip law, stated as a testable property:**

- **L1 (structured → packed → structured is identity):** for every `a: NdAddr` whose every field is in profile range, `nd_addr_of_ppn(nd_ppn_of(a)) == a`.
- **L2 (packed → structured → packed is identity):** for every `p: FtlPpn` with `ftl_ppn_in_range(p, g)`, `nd_ppn_of(nd_addr_of_ppn(p)) == p`.
- **L3 (no aliasing):** `nd_ppn_of` is injective over in-range addresses — two distinct in-range `NdAddr`s never pack to the same `FtlPpn`.
- **L4 (field independence):** changing exactly one dimension changes the packed value in exactly that dimension's bit range and no other.

L1/L2 are exhaustively checkable at `fw/`'s v1 geometry (4096 pages) and at `emu/`'s (128) — an exhaustive property test, not a sampled one. L3/L4 follow from disjoint bit ranges but are asserted anyway, because they are what breaks first when a profile changes a field width. These live in a new `fw/addr_algebra_check.spl` alongside the existing `nd_types_check.spl`.

**Honesty constraint inherited from `nd_types.spl`:** the packed layout allocates bits only for dimensions with real conversion math. `way`/`bank`/`plane` get **zero-width fields** in v1, not fake ones, and `nd_addr_of_ppn` continues to return index 0 for them — preserving the assertion at `nd_types_check.spl:120,122`.

---

## 4. PROPOSED — interaction with the rest of the master plan

### 4.1 Workstream A (HWIR offload) — the strongest argument for this work

Master plan §2 (2026-09-01 correction) measured the strict lowering: `lower_strict_mir_function_to_hwir` accepts **u32/i32/Bool/Bits scalars** and binops **and/or/shl/shr only** (`strict_mir_comb_op`, `mir_to_hwir.spl:191-197`) — no add, no xor, no `/`, no `%`, one basic block.

The address codec is therefore, precisely:

- **`i64` + `/` + `%` (today, `nvme_types.spl:122-131`): not offloadable, on two independent grounds** — wrong scalar width *and* forbidden operators.
- **u32 + `shl`/`shr`/`and`/`or` (§3.7): offloadable as written, today, without waiting for A's comb-op widening.**

That is a real and unusually cheap win. A's first increment is ECC under the equivalence gate, and ECC "needs add/xor + if-conversion". The **address codec needs neither** — it is a pure single-block bit-shuffle over fixed-width scalars, which is exactly the shape the strict lowering already admits. *(inferred, and the highest-value thing for A to check)*: `ftl_ppn_to_nd_addr` / `nd_ppn_of` may be the *first* NVMe firmware unit that lowers to HWIR at all, ahead of ECC, and would therefore make a better pilot for the three-way equivalence gate — the vector space is small enough to enumerate exhaustively (4096 at v1 geometry), which is the ideal first gate subject.

This makes the u32 migration (§4.4) not a stylistic preference but a **precondition for offload**, and it is the argument that should carry this workstream's priority.

### 4.2 Workstream C (four-axis profiles) — where the range checks come from

§3.4's validated constructors need bounds, and §1.4-C8 measured that `OpenSsdConfig`'s geometry fields are descriptive only: the RV32 profiles declare `blocks: 2, pages_per_block: 1` (`openssd_config.spl:137,164`) while `fw/`'s address helpers use the compile-time `NUM_BLOCKS=64` / `PAGES_PER_BLOCK=64` unconditionally.

**Proposal:** a `FtlGeometry` / `NdGeometry` value, derived from C's validated `ProductProfile`, is threaded to every constructor and every conversion (§3.5's `g` parameter). Bit widths in §3.7 are computed from it. Concretely this replaces three duplications with one source: `NUM_CHANNELS` (`fil_scheduler.spl:21`), `ND_NUM_CHANNELS` (`nd_types.spl:110`), and `OpenSsdConfig.channels` (`openssd_config.spl:28`) all become reads of the profile — retiring C4 by construction rather than by an anti-drift check.

**Ordering:** C's profile binding must land before the constructors can be genuinely validated. Until then, constructors validate against the current constants and the gate records the debt. The typed constructor is still worth landing first, because it creates the single place the profile later plugs into — 202 call sites do not have to be revisited twice.

### 4.3 Workstream G (RegisterIR / PinIR generators) — address types should be generated

Hand-writing a per-profile type set is exactly the duplication this whole plan exists to kill. **Proposal: `AddrIR` — a sixth IR in G's single-source family.** One `.sdn` declaration per layer namespace names each coordinate, its parent dimension, its bit width (or a profile expression for it), and its role suffix; G's generator emits, from that single source:

1. the struct declarations for all five namespaces,
2. the validated / clamping / trusted constructors, bounds-checked against the profile,
3. the packed↔structured codec with the bit layout,
4. the `*Opt` companions (§3.6),
5. the round-trip property tests (§3.7's L1-L4) as generated `_check.spl` content,
6. the gate's enumerated-signature allowlist (§6) — so the gate and the types cannot drift.

This is the same generator shape G already proposes for RegisterIR (register → accessor + constraint + doc + test content), applied to coordinates. Generated types also settle §3.4's "generated constants should create compile-time values" clause of hardening §9.3, which hand-written constructors cannot.

**Ordering:** the design in §3 must be hand-validated on one namespace (`Nd`, which already exists) before the generator is written. Generate second, not first.

### 4.4 Workstream D (payload widening) — one migration, not two

D widens the payload from a single `i64` word to a 4096-byte page. That change and this one touch the **same signatures**: `fil.program(ppn: i64, lba: i64, seq: i64, data: i64)` (`fil.spl:104`) has both an address problem and a payload problem in one line, and `dram.stage(span, index, byte)` (`dram.spl:125`) likewise.

Three reasons they must be sequenced as one effort:

1. **Same call sites.** Touching `fil.program`'s 18 address sites and then its payload parameter is two rounds of the same review over the same 72 files.
2. **`UNMAP = -1` blocks both.** A 4096-byte payload implies a sector/offset coordinate (`HstSector`, `NdSector`), and a u32 address space (§4.1) has no room for `-1`. §3.6's `Opt` types must land *before or with* D, not after.
3. **The `_check.spl` suite is shared.** Both migrations keep the same green bar; running them serially doubles the number of times each check file is rewritten.

**Proposal:** a joint sequencing table between I and D, layer by layer, in which each commit changes both the address types and the payload type of the signatures it touches. §5's ordering is written to accommodate this.

### 4.5 Workstream B (MDSOC+ layering)

§3.2's namespaces are the *data* half of B's dimension boundary: B's rule "typed block ops, no NAND coords visible at the HOST boundary" becomes mechanically checkable once `Nd*` and `Hst*` are distinct type names — a `use`-graph gate can assert that no `Hst`-layer module names an `Nd*` type. This is a cheap addition to the fail-closed `use`-graph gate B is already building as its interim substitute, and it works *without* nominal typing, since it is a text/import property.

B's two measured layering violations are also address-typing violations, and are fixed by the same change: `rain.spl:15` and `openssd_config.spl:9` import `fil_scheduler` only for `NUM_CHANNELS` — §4.2 removes that import entirely by sourcing the channel count from the profile.

---

## 5. PROPOSED — full-conversion migration plan

### 5.0 Principles

- **Bottom-up.** The NAND-device layer is the only one with landed types and live consumers, so it is the fixed point everything else converts toward.
- **One layer per commit.** Each commit leaves every `*_check.spl` in `fw/` green — the existing suite is the regression bar and is not weakened, skipped, or rewritten to accommodate a migration step.
- **Each commit is a forward delta on signatures only.** No behaviour change is permitted in a conversion commit; a commit that fixes a bug found during conversion is a separate commit with its own reproduce spec (per the standing "fixes need reproduce + similar tests" rule).
- **The gate's baseline ratchets down every commit and never up.**

### 5.1 Steps

| # | Commit | Scope | Green bar | New gate baseline |
|---|---|---|---|---|
| 0 | **Prerequisite: land the gate advisory-red** | `scripts/check/check-typed-address-algebra.shs` + baseline 202 | selftest fatal, sabotage red | 202 |
| 1 | **`Nd` completion** | finish `nd_types.spl`: validated constructors, `NdGeometry`, bit-packed codec (§3.7), L1-L4 property tests in a new `addr_algebra_check.spl` | `nd_types_check.spl` + new file | 202 (no signatures changed yet) |
| 2 | **FIL device layer** | `fil_nand.spl`, `fil_nand_device.spl`, `fil_fmc.spl`, `fil_ecc.spl`, `fil_badblock.spl` → `Nd*` types | `fil_nand_emu_check.spl`, `ecc_check.spl` | ≈157 |
| 3 | **FIL scheduler** | `fil_scheduler.spl`, `fil.spl`: `FilCh`, `FilWay`, `FilCeReady`; retire C5's mixed signatures | `parallelism_check.spl`, `rel_*_check.spl` | ≈135 |
| 4 | **`FtlPpnOpt` / `FtlBlkOpt`; delete `UNMAP`/`NO_PPN`/`NULL_IDX`** | `nvme_types.spl:30-40` + ~40 sites in `ftl.spl` + `ftl_band.spl` + `fil.spl` | `gc_safety_check.spl`, `durability_check.spl`, `format_check.spl` | ≈135 (signature count flat; the win is C1) |
| 5 | **FTL core** | `ftl.spl` (33), `ftl_map.spl` (7), `ftl_band.spl` (14), `ftl_gc.spl`, `ftl_journal.spl`, `hooks.spl` | `rain_ftl_check.spl`, `gc_safety_check.spl`, `policy_hooks_check.spl` | ≈74 |
| 6 | **RAIN** | `rain.spl`: `FtlGroup`, `FtlStripe`, `FilCh`; retire the third `NUM_CHANNELS` | `rain_check.spl` | ≈69 |
| 7 | **HOST layer (jointly with D)** | `hil.spl`, `hil_command.spl` (incl. C6's `HstPrpPair`), `hil_queue.spl`, `nvme_types.spl` cmd/cpl, `dram.spl` | `host_transport_check.spl`, `hil_queue_backpressure_check.spl`, `dram_buffer_check.spl` | ≈40 |
| 8 | **Admin / queue-set / controller** | `nvme_admin.spl` (19), `nvme_qset.spl` (18), `nvme_controller.spl` (5), `nvme_admin_types.spl` | `qset_delete_check.spl`, `nvme_controller_gc_check.spl` | 0 |
| 9 | **Profile binding (needs C)** | replace all compile-time geometry constants with `FtlGeometry`/`NdGeometry` reads | full `fw/` suite | 0, plus a new "no compile-time geometry constant in an address path" rule |
| 10 | **u32 narrowing (enables A)** | `idx: i64` → `idx: u32` throughout; codec to `shl`/`shr`/`and`/`or` | full suite + A's equivalence gate on the codec | 0, plus "no `i64` field in an address struct" |
| 11 | **Generate (needs G)** | replace hand-written types with `AddrIR`-generated ones; assert byte-identical output first | full suite | 0 |

Steps 9-11 depend on other workstreams and are sequenced last deliberately; steps 0-8 are self-contained and can start immediately.

### 5.2 Two ordering hazards, stated rather than discovered later

- **Step 4 before step 10 is mandatory.** `-1` has no u32 representation; narrowing before the sentinels are gone converts a visible sentinel into silent wraparound.
- **Step 1 before everything.** Converting call sites against constructors that do not yet validate produces 202 edits that must be revisited when the validation lands.

---

## 6. PROPOSED — the completion gate

`scripts/check/check-typed-address-algebra.shs`, written in `.shs` (no Bash/Python), modelled on `scripts/check/check-no-direct-rt.shs` — a **ratchet with a baseline file**, not a hard zero-bar, because a hard bar cannot be landed against a tree with 202 offenders.

Deliberately **not** lint-based: `bin/simple lint` costs ~12s startup plus a superlinear per-declaration term (`.claude/rules/commands.md`), and — per §0 — does not check types anyway.

### 6.1 What it checks

1. **Bare-`i64` address parameters.** Scans `fw/*.spl` for `(fn|me) name(... <address-role-name>: i64 ...)` where the parameter name matches the enumerated role list (`lba|ppn|vpn|blk|block|page|wl|wordline|ch|channel|way|lun|bank|plane|band|stripe|group|slot|qslot|prp|sector|nsid|cid|qid|addr|index`). Counted against `scripts/check/typed_address_baseline.txt`; **any increase FAILs**.
2. **Stale baseline.** A baselined site that is no longer an offender also FAILs — the same both-directions rule as `check-unbacked-extern-ratchet.shs`. A baseline that no longer describes the tree is how a ratchet silently stops ratcheting.
3. **Bare struct-literal construction.** `<AddrType>(idx:` appearing outside the owning constructor module is a violation with no baseline escape from step 1 onward. This is the honest substitute for private fields (§2.4).
4. **`*_trusted` call-site count**, ratcheted against its own baseline — the escape hatch of §3.4 cannot silently grow.
5. **Sentinel ban**, from step 4 onward: `UNMAP`, `NO_PPN`, `NULL_IDX` must have zero occurrences in `fw/`.
6. **Cross-namespace conversion without a named function**, from step 3 onward: an `Nd*` type named inside a `Hst*`-layer module, or vice versa, is a violation (this is the §4.5 hook, and it works without nominal typing).

### 6.2 Verdict convention (repo standard)

| verdict | exit |
|---|---|
| `PASS — <n> signature(s) checked in <k> file(s), forbidden=<f> (baseline <b>)` | 0 |
| `FAIL — <n> signature(s) checked, <m> new offender(s): <names>` | 1 |
| `ERROR — nothing was checked (<reason>)` | 2 |

**Non-vacuity is absolute:** a run that scanned 0 signatures, or found 0 `fw/*.spl` files, is **ERROR, never PASS**. A run that cannot read the baseline is ERROR. The verdict line is the last line of stdout and always states how many things were examined, so a vacuous run cannot be mistaken for a real one.

### 6.3 `--selftest` — fatal, runs before every scan

Every fixture is a real file tree fed to the real scanner:

1. clean fixture (all address params typed) → must PASS;
2. **sabotage:** one `fn f(lba: i64)` added above baseline → must FAIL, naming `lba`;
3. **sabotage:** a bare `FtlBlk(idx: 3)` literal outside the constructor module → must FAIL;
4. **sabotage:** a baselined offender removed without a baseline update → must FAIL as stale;
5. **sabotage:** a `UNMAP` reintroduced after step 4 → must FAIL;
6. **sabotage:** an `NdBlock` named inside a `Hst`-layer fixture module → must FAIL;
7. empty tree → must scan 0 signatures, forcing the caller to ERROR;
8. **sabotage of the counter itself:** a fixture where the pattern matches inside a comment or a docstring → must NOT be counted (false-positive guard, so the gate cannot be satisfied by moving code into comments).

**Every gate needs a sabotage proving it turns red**, and fixture 8 is the one that proves the gate is not trivially satisfiable — the failure mode a text-based gate is most prone to.

### 6.4 Completion

The workstream is complete when the baseline reads **0** for check 1, checks 3-6 are unconditional, and `--selftest`'s eight fixtures pass — **and** when either (a) a nominal argument-type check exists in the compiler, or (b) §7's feature request is filed, linked from this document, and the gate is wired into `pre-push-conflict-tree-guard.shs`. Absent (a), the gate is the only thing standing between this design and its silent erosion, so (b) is not optional.

---

## 7. Bugs and feature requests this workstream must file

Per CLAUDE.md ("fix it or record a concrete bug/feature request instead of silently normalizing the workaround"), the measurements in §0 and §2 are not workarounds to route around:

1. **FEATURE — nominal argument-type checking.** Measured: `takes_i(x: i64)` accepts `"hello"` and prints a raw pointer; `newtype`, single-field-struct and `newunit` wrappers are all interchangeable at call sites; `lint` and `SIMPLE_JIT_STRICT=1` both pass all of it. Without this, no typed-address design in this repo is enforceable, and the master plan's "make the invalid state unrepresentable" posture is unavailable language-wide. **On the critical path for workstream I.**
2. **BUG — `newunit` silently rewrites the value it wraps (×8 = `<< 3`).** Measured: with `newunit LbaU: i64 as lbau` / `newunit PpnU: i64 as ppnu`, `takes_lba(p_ppnu_7)` returns **56** and `takes_lba(5)` returns **40**. This contradicts `test/03_system/app/compiler/feature/world_units_newunit_spec.spl` (REQ-WUN-001), which asserts a nominal 1:1 wrapper with `base_factor` 1/1. Two candidate causes to distinguish when triaging: a wrongly-applied cross-unit conversion factor, or a 3-bit value tag leaking through the wrapper. Either way a wrapper that rewrites its own value is a corruption source, and severity is high independent of this workstream.
3. **DOC BUG + SEVERITY AMPLIFIER — `src/compiler/35.semantics/lint/primitive_classification.spl:86`** asserts *"`newtype` does not exist"*, contradicted by `tokens.spl:167,332,416`, both parsers, `test/01_unit/compiler/newtype_ops_spec.spl`, and this session's execution. **This is not merely a stale comment:** the `DomainWrapperCatalog` immediately beneath it (`:96-120`) is the compiler's *own lint suggestion machinery*, and `DomainWrapper.declaration()` (`:88`) emits `newunit <Name>: <T>` as the recommended fix — for `PhysAddr: u64`, `VirtAddr: u64`, `MemOffset: u64`, `IrqVector: u16`, `FileHandle: u32`. Per finding 2, the linter is therefore actively recommending a value-scaling construct **for physical and virtual memory addresses** — the exact class of value where a silent ×8 is catastrophic, and the exact class this workstream is about. Findings 2 and 3 should be triaged together.
4. **DEBT — private fields unverified.** Hardening §9.3 requires "constructors must be private or validated"; this design delivers only "validated" (§2.4, §3.4), with the gate covering the rest. Recorded as a known shortfall, not claimed as satisfied.

## 8. Evidence caveats

- All executions used `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`, which **self-identifies as the Rust bootstrap seed** ("do not use it as the normal tool"). Per `.claude/rules/commands.md` the default tooling should be the pure-Simple self-hosted binary; per `.claude/rules/vcs.md` no full-CLI pure-Simple binary is currently deployed and all four tracked stage binaries SEGV on hello world. **The §0 and §2 probes therefore could not be re-run on a self-hosted binary and must be re-measured when one is deployed.** *(inferred)*: the type checker is shared source, so the results are expected to hold — but that is an inference, not a measurement, and finding 1 above should not be closed on it.
- The 202-site count is a grep over parameter declarations only. Struct fields, return types, array element types, and locals are excluded and will raise the true conversion volume. Workstream J's census supersedes this number when it lands.
- The `emu/` and `fw_rv32/` trees were surveyed for coordinate spaces (C7) but not censused; they are out of migration scope.
