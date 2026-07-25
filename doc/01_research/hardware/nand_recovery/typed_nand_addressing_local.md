# Typed NAND Addressing — Value Types for Physical-Address Dimensions (Local Research)

**Status:** research. Scope: whether/how to replace raw `i64` physical-address
coordinates (channel, way/CE, bank/LUN, plane, block, wordline, page) in
`examples/09_embedded/simpleos_nvme_fw/fw/` and the `rel_*` reliability engine
with typed value structs, following this repo's existing custom-typed-layer
convention. No code is changed by this doc.

Ground truth read: `doc/07_guide/lib/algorithms/typed_alpha_algorithm_layers.md`
+ `src/lib/common/crypto/typed/ctypes.spl` (newtype pattern); the FW/emulator
source itself (address-math site inventory, §2); the taxonomy
(`nand_ssd_recovery_prevention_taxonomy.md`) + the already-landed
`doc/04_architecture/hardware/nand_recovery/reliability_engine_architecture.md`
(dimension keying, §3); the `nand_emu` research doc §1
(`nand_emu_fpga_riscv_emulator.md`, single-chip topology facts). No other
literature is invented.

---

## 1. Repo convention: how typed layers wrap primitives here

**The newtype pattern (`src/lib/common/crypto/typed/ctypes.spl`).** Each type
is a single-field struct over a primitive payload plus an `impl` block of
free functions — constructor(s), accessors, and (for secret-shaped types only)
constant-time `ct_eq`:

```
struct Digest:
    payload: ByteSpan
impl Digest:
    static fn new(data: [u8]) -> Digest: ...
    fn bytes() -> ByteSpan: ...
    fn ct_eq(other: Digest) -> bool: _ct_eq_spans(self.payload, other.payload)
```

`Digest`/`MacTag`/`Nonce`/`AuthTag`/... (ctypes.spl:94-352) all share this
shape. `doc/07_guide/lib/algorithms/typed_alpha_algorithm_layers.md` names the
governing rule: **"Reuse these — do not reimplement an algorithm or invent a
parallel primitive type"** and these layers live in **new, additive
namespaces** that wrap existing cores rather than editing their signatures
("wrap, don't rewrite" — line 12) so a hot parallel session's existing module
is never touched. This is the model for the address-dimension types proposed
in §4: new files, no edits to `nvme_types.spl`'s existing signatures.

**A second, DIFFERENT pattern that must not be conflated with the above:
integer `val` constant dispatch.** `nvme_types.spl` declares dozens of typed
module-level constants with the `val NAME: i64 = LITERAL` const-declaration
form — opcodes (`val OP_READ: i64 = 0x02`, line 16), status codes (`val
SC_SUCCESS: i64 = 0x00`, line 21), lifecycle states (`val BLK_OPEN: i64 = 1`,
line 57), write-task phases (`val PH_ALLOC: i64 = 1`, line 63) — dispatched
via plain `if`/`==` on the `i64`, never via a payload-carrying `enum`. This is
orthogonal to the newtype-struct pattern above: it is how the repo does
*primitive constant dispatch* (partly to sidestep the "anonymous tuple /
payload enum decay" interpreter landmine — `.claude` agent guide, "Language
landmines"), not how it wraps a value in a distinct type. Plain no-payload
enums with `match` (`NeProfile`, `NeOobPolicy` — `nand_types.spl:21-38,70-86`)
are the dispatch-safe middle ground the emulator already uses. The
address-dimension types in §4 belong to the **newtype-struct** axis (they add
compile-time distinctness over an `i64`), while any FSM/state values they
carry stay on the **`val`-constant** axis.

**Value-type law and its cost consequence.** Arrays and structs are copied by
value on parameter pass (repo law); this is independently reinforced in the
FW source itself — `fil_nand_emu.spl:114`: `# (return-the-object; chip is a
value type)`, applied to `NeChip`, a struct with many more fields than any
single address-dimension wrapper. A single-`i64`-field `NdBlock`/`NdPage` is
therefore *strictly cheaper* to copy than a pattern the repo already treats as
free — no heap payload, no traversal, just an `i64`-sized copy. The one real
cost is the "return-the-object" landmine: a helper that appears to "mutate" a
value-type struct must return the new value and the caller must reassign.
This is not a new landmine invented by this proposal — it is the same class
already documented for arrays (`feedback_arrays_value_types` memory: "Objects
… are passed by reference — only arrays [and structs] have this value-type
behavior") and already followed by every `ctypes.spl` method (every call
returns a fresh/self value, never mutates in place).

**Naming / collision law.** Same struct name in two modules is an interpreter
global-registry collision (repo law). `nand_emu` reserves `Ne`
(`nand_types.spl:7`); the reliability engine reserves `Rel`
(`reliability_engine_architecture.md:66-69`, "all public types prefix `Rel`
… same rule as the emu's `Ne` prefix"). A typed-addressing layer needs its
**own** prefix, distinct from both — `Nd` (Nand-Dimension) is proposed in §4.

---

## 2. Current address math: site inventory

Base paths: FW = `examples/09_embedded/simpleos_nvme_fw/fw/`, NE =
`src/lib/hardware/nand_emu/`. Found by a consolidated grep sweep for raw
`*`/`/`/`%` arithmetic against `PAGES_PER_BLOCK`, `NUM_CHANNELS`,
`geo.pages_per_block`, plus every callsite of the canonical helpers
(`ppn_block`/`ppn_page`/`block_first_ppn`). **23 distinct address-arithmetic
sites** (canonical helpers + raw/duplicated compositions; plain call-sites of
a canonical helper — dozens, in `fil.spl`, `ftl_band.spl`, `fil_nand.spl`,
`fil_nand_device.spl`, `fil_fmc.spl` — are correct usage and excluded from
this count).

### FW (13 sites)

| # | Site | What |
|---|---|---|
| 1 | `nvme_types.spl:113-114` | `ppn_block(ppn) = ppn / PAGES_PER_BLOCK` — **canonical**, widely called |
| 2 | `nvme_types.spl:116-117` | `ppn_page(ppn) = ppn % PAGES_PER_BLOCK` — **canonical**, widely called |
| 3 | `nvme_types.spl:119-120` | `block_first_ppn(blk) = blk * PAGES_PER_BLOCK` — **canonical**, widely called |
| 4 | `fil_scheduler.spl:28` | `channel_of(blk) = blk % NUM_CHANNELS` — **canonical** (`NUM_CHANNELS = 8`, line 21) |
| 5 | `rain.spl:69-70` | `rain_num_groups() = NUM_BLOCKS / NUM_CHANNELS` |
| 6 | `rain.spl:79-83` | `rain_ppn(group, channel, page) -> ppn` — 3-level compose: `blk = group*NUM_CHANNELS+channel`, `ppn = blk*PAGES_PER_BLOCK+page` |
| 7 | `rain.spl:86-91` | `rain_stripe_idx(ppn) -> stripe` — 3-level decompose via `ppn_block`/`ppn_page` |
| 8 | `ftl.spl:397` | `rain_seal`: `me.rain_parity[group*PAGES_PER_BLOCK+page]` — **inline duplicate** of the `rain.spl:91` shape |
| 9 | `ftl.spl:442` | `rain_recover_channel`: `blk = group*NUM_CHANNELS+failed` — **inline duplicate**, bypasses `rain_ppn` |
| 10 | `ftl.spl:466` | `rain_recover_channel`: `ppn = blk*PAGES_PER_BLOCK+page` — **inline duplicate**, bypasses `block_first_ppn` |
| 11 | `fil_nand_emu.spl:78-85` | `emu_fold_row(fw_ppn, geo)`: FW ppn → emu S1 row. Re-derives `blk = fw_ppn / PAGES_PER_BLOCK`, `page = fw_ppn % PAGES_PER_BLOCK` **raw**, instead of calling `ppn_block`/`ppn_page` |
| 12 | `fil_nand_emu.spl:87-89` | `emu_fold_blk(fw_blk, geo)`: FW block → emu S1 block (`fw_blk % geo.blocks`) |
| 13 | `fil_nand_emu.spl:91-93` | `emu_first_row_of_blk(ne_blk, geo)`: `ne_blk * geo.pages_per_block` — duplicates the `block_first_ppn` shape in emu-row space |

Sites 11-13 are **the FW ↔ emulator address seam** — the exact boundary a
typed adapter would sit at (§4.3).

### Emulator (10 sites)

| # | Site | What |
|---|---|---|
| 14 | `geometry.spl:54-58` | `ne_cell_index(row,col,bit,page_bytes) = ((row*page_bytes)+col)*8+bit` — 3-level compose into the Vt byte array |
| 15 | `geometry.spl:70-87` | `ne_decode_address`: 5-cycle address latch → `(col,row)` bit-packing (doc §1.2) |
| 16 | `geometry.spl:89-95` | `ne_decode_address_erase`: 3-cycle latch → `row` only |
| 17 | `geometry.spl:101-108` | `ne_col_effective`: column fold. **Historically buggy site** — the doc comment records the exact regression: `col & (page_bytes-1)` corrupted in-range columns because `page_bytes` (528/4224) is not a power of two (`291 & 527 = 3`); fixed to `col % geo.page_bytes` on 2026-07-18. This is precisely the "S-profile fold collision" bug class this proposal targets |
| 18 | `geometry.spl:110-135` | `ne_row_effective`/`ne_row_in_window`: row fold + `NeOobPolicy` (Alias/Window/Trap) |
| 19 | `chip.spl:171-173` | `ne_block_of(row, geo) = row / geo.pages_per_block` — block-only helper (no companion page-in-block helper exists) |
| 20 | `chip.spl:383` | `page_in_blk = row - (blk_idx * geo.pages_per_block)` — **inline**, no shared helper |
| 21 | `chip.spl:452` | `first_page = blk_idx * geo.pages_per_block` — **inline duplicate** of "first row of a block" (same shape as FW site 13, no shared code between the two layers) |
| 22 | `chip.spl:777` | `set_factory_bad_blocks`: `row = blk * geo.pages_per_block + pg` — another **inline duplicate** of the same shape |
| 23 | `vt_array.spl:28` | `geo.page_bytes * 8 * geo.total_pages` — Vt-array total-size formula, the root the cell-index formula (site 14) is bounded by |

**Pattern:** the block/page split (`/`, `%`, `*PAGES_PER_BLOCK`) is
independently reimplemented at minimum **four** times (nvme_types canonical,
rain.spl's own consistent-but-separate copy, `ftl.spl`'s raw bypass, and
`fil_nand_emu.spl`'s raw re-derivation) — any one of which can drift from the
others if `PAGES_PER_BLOCK` or the split direction ever changes. This
duplication, not a hypothetical, is the concrete bug surface a typed
composer/decomposer pair removes.

---

## 3. Topology facts + which `rel_*` policy keys on which dimension

**Target hierarchy** (SSD-controller levels above a single chip, then
single-chip levels below, per the task brief and the K9F8G08X0M datasheet
facts in `nand_emu_fpga_riscv_emulator.md` §1.1):

```
channel → way/CE (die) → LUN/bank → plane → block → wordline → page
```

- **channel / way** are SSD-controller-level (multiple channels, each with
  several CE-selected dies/ways sharing the bus) — not modeled in a
  single-chip datasheet at all; this is the FW-side, multi-chip half of the
  hierarchy.
- **plane / block / page** are inside one chip. The K9F8G08X0M datasheet facts
  (`nand_emu_fpga_riscv_emulator.md:32-58`): 2 planes × 2,048 blocks = 4,096
  blocks, 64 pages/block = 262,144 pages; plane is one bit of the row address
  (A19, doc §1.2 line 57). `nand_emu`'s v1 chip model is explicitly
  **single-plane**: two-plane commands are recognized-but-unsupported
  (`NeViolation.UnsupportedCommand`, `nand_types.spl:185`), so plane exists in
  the datasheet contract but has no addressable typed representation in code
  today.
- **LUN/bank** (multiple planes-groups per die in ONFI terms) has **zero**
  mentions anywhere in `fw/` or `nand_emu/` (confirmed by grep) — purely a
  target-hierarchy concept, not yet load-bearing anywhere in this repo.

**Page vs. wordline — the reason they must be two distinct types.** v1 is
SLC: 1 bit/cell, 1 page per wordline (`chip.spl:71-73` `ne_sense_bit`;
`nand_types.spl:48` `sectors_per_page=1` for S1). Nothing in the emulator
research doc or code names "wordline" as a concept distinct from "page" —
`page` and `wordline` are numerically identical in v1. MLC/TLC (v2+) pack
2-3 pages per wordline (lower/middle/upper page), so **if `NdWordline` is
defined as a type alias of `NdPage` now, the v1→v2 MLC upgrade silently
breaks** every policy keyed on wordline once page:wordline stops being 1:1 —
exactly the landmine class the task brief calls out.

**Live vs. declared-but-not-load-bearing vs. not-yet-modeled**, per the site
inventory (§2) and `openssd_config.spl` (`channels`/`ways_per_channel` fields,
lines 20-21, 41-42, 63-64, 85-86):

| Dimension | Status today |
|---|---|
| channel | **LIVE** — drives `channel_of`/RAIN stripe math (FW site 4, 6-10) |
| block | **LIVE** — drives every `ppn_block`/`block_first_ppn` call and `ne_block_of` |
| page | **LIVE** — drives `ppn_page` and the emu row-in-block arithmetic |
| way | **DECLARED, NOT LOAD-BEARING** — `ways_per_channel: 2/8` fields exist in `OpenSsdConfig` (lines 21, 64, 86) but `blocks: NUM_BLOCKS` stays the same flat 64-block constant regardless of channel/way count — way never multiplies into any address today |
| bank/LUN | **NOT MODELED** — zero references anywhere |
| plane | **NOT MODELED** — datasheet fact only (`nand_emu_fpga_riscv_emulator.md:39,57`); `NeViolation.UnsupportedCommand` for two-plane ops |
| wordline | **NOT MODELED** — collapses to `page` in v1 SLC; no code names it |

**Which `rel_*` reliability policy keys on which dimension** (taxonomy scheme
names cited from `nand_ssd_recovery_prevention_taxonomy.md`; v1/v2 scoping
confirmed against the already-landed
`doc/04_architecture/hardware/nand_recovery/reliability_engine_architecture.md`):

| Policy (`rel_*` module) | Keys on | Taxonomy anchor | Notes |
|---|---|---|---|
| `rel_vref` (ROR-lite calibration) | **block** | §2.1 read-retry, §2.2 "ROR … learns the optimal read-reference voltage for each block" (taxonomy:101-102) | architecture doc: "per-block calibrated-offset cache" (line 60) |
| `rel_disturb` (STRAW-lite) | **block in v1**; **wordline is the named v2 gap** | §3.4 "STRAW: tracks accumulated read-disturb stress by wordline" (taxonomy:650-652) | architecture doc line 62/310: "block-granular in v1; per-wordline is v2" — this is the concrete, already-documented consumer `NdWordline` would unblock |
| `rel_wear` (SREA-lite static WL) | **block** | §3.7 "Dynamic/Static wear leveling: select … blocks" (taxonomy:744-747); plane/die/channel/wordline/layer-aware variants named but out of v1 scope (taxonomy:750-756) | architecture doc line 63 |
| RAIN parity (`rain.spl`) | **channel** (stripe = one page per channel) | §2.8 "Stripe parity across channels" (taxonomy:349) | already channel-typed in spirit via `rain_ppn(group,channel,page)` (site 6) |
| Layer/wordline-variation recovery (LaVAR — not yet a `rel_*` module) | **wordline-group / layer** | §2.3 "Per-wordline calibration: tracks the error behavior of individual wordlines" (taxonomy:129); "Die/chip-specific calibration" (taxonomy:134-135) | explicitly out of v1 scope (single-chip, SLC); the reason `NdWordline` must exist as its own type even though it is inert today |

---

## 4. Recommendation

### 4.1 Proposed newtype set

Following the `ctypes.spl` shape exactly (single-field struct + `impl` block
of free functions), field name **`idx`** (not `val` — `val` is a reserved
keyword used for const declarations, see §1; not `payload` — that name is the
crypto layer's convention for a `ByteSpan`, these wrap a plain `i64`):

```
struct NdChannel:  idx: i64
struct NdWay:       idx: i64   # CE / die within a channel
struct NdBank:      idx: i64   # LUN within a way
struct NdPlane:     idx: i64   # plane within a bank
struct NdBlock:     idx: i64   # erase block within a plane
struct NdWordline:  idx: i64   # wordline within a block (SLC v1: == NdPage numerically, but a DIFFERENT type)
struct NdPage:       idx: i64   # page within a wordline (1:1 in v1 SLC, 2-3:1 in v2 MLC/TLC)

struct NdAddr:
    channel: NdChannel
    way:     NdWay
    bank:    NdBank
    plane:   NdPlane
    block:   NdBlock
    page:    NdPage
```

Plus flat-`ppn`/`row` converters mirroring the existing canonical helpers:
`NdAddr.from_ppn(ppn: i64) -> NdAddr`, `.to_ppn() -> i64` (wrapping today's
`ppn_block`/`ppn_page`/`block_first_ppn`), and — on the emu side, as an
adapter, not a redefinition — a converter from `NdAddr`/`NdBlock`/`NdPage`
into the `NeGeometry`-shaped `row` the chip API already uses.

Only ship what has a live caller now (repo law: never add unused code) —
**`NdChannel`, `NdBlock`, `NdPage`, `NdAddr` (channel+block+page only) land
first**, since those are the three LIVE dimensions (§3 table). `NdWay`,
`NdBank`, `NdPlane`, `NdWordline` are specified here (so the type names and
shape are fixed and reviewed once) but are **not landed as code** until a
real consumer exists — the OpenSSD 8-way board profile actually multiplying
`ways_per_channel` into an address, v2 plane support, or a `rel_disturb`
wordline-granular mode. This mirrors the "new code typed from day one, don't
scaffold ahead of a consumer" migration principle in §4.3.

### 4.2 Placement

**A new leaf module** in `fw/` (proposed name `nvme_addr.spl`), a **peer** to
`nvme_types.spl` and the already-landed `rel_types.spl` — not folded into
`nvme_types.spl` itself. Two independent reasons converge on this:

1. `nvme_types.spl`'s own header (line 4) states its scope: **"Pure data +
   constants + small free helpers. NO `impl`/`me` methods here, so this
   module is cheap to type-check and safe to import everywhere."** The
   newtype pattern in §1 requires `impl` blocks (constructors, converters) —
   structurally incompatible with that file's contract. Adding `impl` there
   would violate the file's own stated invariant, not just style.
2. The import-graph fact from `reliability_inventory.md` §C — `ftl` imports
   `fil`; `fil` never imports `ftl`; both share the `nvme_types` leaf — and
   the now-landed `reliability_engine_architecture.md` §1 diagram, which puts
   `rel_types.spl` at exactly this same depth ("mirrors `nand_types.spl`'s
   role for the emu", using `nvme_types.*` only, importable by both `fil` and
   `ftl` without a cycle). A typed-addressing leaf at the same depth —
   depending only on `nvme_types` — is importable by `fil.spl` (device-near
   actuation), `ftl.spl` (mapping-aware scheduling), and every `rel_*` module,
   exactly like `rel_types.spl` already is. It becomes a **third** peer leaf
   beside `nvme_types`/`rel_types`, not a fourth layer.

`nand_emu`'s `Ne`-prefixed geometry stays exactly where it is — chip-internal
only (plane/block/page; no channel/way/bank, confirmed §3, since a single
chip datasheet has no such concept). The two type families are not an
accident of naming: they cover **different scope** — `Nd*` is the
SSD-controller-wide, multi-chip address space; `Ne*` is one chip's internal
geometry. The conversion between them belongs at the **existing FW↔emu seam**
that already does this job informally: `fil_nand_emu.spl`'s
`emu_fold_row`/`emu_fold_blk`/`emu_first_row_of_blk` (site 11-13, §2) is
where an `NdAddr → NeGeometry`-row adapter naturally lands.

### 4.3 Migration strategy — additive, seam-based, not big-bang

Principle (matches §1's "wrap, don't rewrite" and the NVMe fw hardening bar's
"every fix needs a regression assertion"): **new code is typed from day one**
(any future `rel_*` observation struct field that names a block/page/channel
uses `NdBlock`/`NdPage`/`NdChannel`, not `i64`); **existing fw address math is
converted only at natural seams**, one seam per change, each landing with its
own `*_check.spl` regression assertion — never a single sweeping rewrite of
`nvme_types.spl`'s widely-called helpers.

**Top 5 highest-value existing sites to convert first**, ranked by leverage
(how many other sites route through it) and by which sites are the actual bug
surface (raw duplication that already drifted once — §2's S-profile fold
collision, `geometry.spl:101-108` — and could drift again):

1. **`nvme_types.spl:113-120`** (`ppn_block`/`ppn_page`/`block_first_ppn`,
   site 1-3) — the root. Add `NdAddr.from_ppn`/`.to_ppn` as thin wrappers
   around the *existing* functions (not replacements) so every current raw-`i64`
   caller keeps compiling; new callers opt into the typed form incrementally.
2. **`rain.spl:79-91`** (`rain_ppn`/`rain_stripe_idx`, site 6-7) — already the
   *correct* pattern (arithmetic isolated behind named functions with a
   3-level composition); the natural first typed consumer since converting
   its signature to take `NdChannel`/`NdBlock`/`NdPage` costs nothing
   structurally.
3. **`ftl.spl:442` and `:466`** (site 9-10) — the concrete duplication-drift
   bug class: these two lines reimplement `rain_ppn`'s and
   `block_first_ppn`'s arithmetic raw, bypassing the helpers that already
   exist. Routing them through the typed composers removes the duplication
   outright and is a pure refactor-at-the-seam (no behavior change, one
   `rel_seams_check.spl`/`ftl.spl`-local regression assertion each).
4. **`fil_nand_emu.spl:78-93`** (`emu_fold_row`/`emu_fold_blk`/
   `emu_first_row_of_blk`, site 11-13) — the FW↔emu adapter seam itself. This
   is where an explicit `NdAddr → Ne-row` converter function replaces the
   raw re-derivation of `blk`/`page` from `fw_ppn`, making the seam the
   single point where FW-typed addressing meets chip-internal geometry — the
   textbook "adapter, not rewrite" migration shape named in the mission brief.
5. **`chip.spl:171-173,383,452,777`** (`ne_block_of` + three inline
   duplicates, site 19-22) — add a companion `ne_page_in_block`/
   `ne_block_first_row` pair (or accept `NdBlock`/`NdPage` directly) to
   collapse the three independent re-derivations of "page within block" /
   "first row of a block" into one call each.

### 4.4 Honest costs

- **No struct-copy benchmark exists in this repo** (grep of `doc/` for
  struct-copy/newtype-overhead notes came up empty) — the cost claim below is
  reasoned from first principles, not measured.
- A single-`i64`-field struct copy is O(1): no heap allocation, no
  traversal, just an `i64`-sized value copy — categorically cheaper than an
  array copy (O(n) in element count), and the repo already treats a much
  larger struct (`NeChip`, dozens of fields) as a free-to-copy value type
  (`fil_nand_emu.spl:114`). `NdBlock`/`NdPage`/`NdChannel` (1 field) and
  `NdAddr` (6 fields, each itself 1 field) are strictly smaller than that
  accepted precedent.
- The **"return-the-object" landmine applies to these structs too**: a
  helper like `fn nd_addr_next_page(a: NdAddr) -> NdAddr` must return the new
  value; the caller must reassign (`a = nd_addr_next_page(a)`), exactly like
  the array landmine already documented in this repo's memory
  (`feedback_arrays_value_types`). This is a known cost class, not a new one,
  and every `ctypes.spl` method already follows this discipline.
- **Unused-code risk**: shipping all 7 dimension types before `way`/`bank`/
  `plane`/`wordline` have a real caller would violate "never add unused
  code." §4.1's phased landing (3 live dimensions first, the rest specified-
  but-not-landed) is the concrete mitigation, not a caveat to revisit later.

---

## References

- Convention: `doc/07_guide/lib/algorithms/typed_alpha_algorithm_layers.md`,
  `src/lib/common/crypto/typed/ctypes.spl`
- FW address math: `examples/09_embedded/simpleos_nvme_fw/fw/nvme_types.spl`,
  `fil_scheduler.spl`, `rain.spl`, `ftl.spl`, `ftl_band.spl`,
  `fil_nand_emu.spl`, `openssd_config.spl`
- Emulator address math: `src/lib/hardware/nand_emu/geometry.spl`,
  `chip.spl`, `vt_array.spl`, `nand_types.spl`
- Topology facts: `doc/01_research/hardware/nand_emu/nand_emu_fpga_riscv_emulator.md` §1
- Taxonomy + keying: `doc/01_research/hardware/nand_recovery/nand_ssd_recovery_prevention_taxonomy.md`
  §2.1-2.3, §2.8, §3.4, §3.7;
  `doc/04_architecture/hardware/nand_recovery/reliability_engine_architecture.md`
  §0, §1, §6
- Placement precedent: `/tmp/claude-1000/-home-ormastes-dev-pub-simple/71ea985c-568c-4d0d-a2a9-ce4ade302864/scratchpad/reliability_inventory.md`
  §C (import-graph facts)
