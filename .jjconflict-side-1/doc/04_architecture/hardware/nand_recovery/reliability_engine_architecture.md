# NAND Reliability Engine — Architecture

**Status:** architecture (2026-07-19). Scope: cell-recovery + failure-prevention
for the `simpleos_nvme_fw` firmware, validated against the `nand_emu` Vt model.

Ground truth: the taxonomy
`doc/01_research/hardware/nand_recovery/nand_ssd_recovery_prevention_taxonomy.md`
(scheme names cited below are from it; no other literature is invented) and the
file:line inventory in the recovery gap analysis. Detail design will follow in
`doc/05_design/hardware/nand_recovery/` and MUST use the interface names fixed
here.

---

## 0. The LAW (design invariant)

> Shared reliability logic lives in **layer-neutral modules placeable on FTL OR
> FIL**. Only logic that *needs FTL-specific information* (L2P mapping, logical
> hotness, GC state) is pinned to FTL.

Two consequences drive the whole design:

1. **Decision and actuation are separate axes.** A policy's *decision inputs*
   (a disturb threshold, an FCR age, a P/E spread) are usually physical-only and
   therefore **placeable**; its *actuation* (re-sense at a shifted Vref vs.
   reclaim/rewrite through the map) decides which layer's handle executes it. The
   verdict seam (§3) is exactly what decouples the two — a policy can be decided
   anywhere and actuated wherever the handle lives.
2. **No policy module ever holds a `Fil` or `Ftl` handle.** Policies are pure
   functions over narrow observation structs returning `RelAction` verdicts. The
   layer that owns the handle (FIL read path, FTL maintenance tick) executes the
   verdict. This keeps the `rel_*` family layer-neutral and unit-testable without
   a device.

This extends the established `hooks.spl` discipline (pure module, `use
nvme_types.*`, no layer handle) — but where `hooks` returns a *scalar score*, a
reliability policy returns an *action*, because recovery and prevention must
actuate, not merely rank (inventory A8: the hooks seam suits scoring, not
actuation). One deliberate difference: `hooks.spl` restricts its slots to
scalar-in/scalar-out because its lambda-registry pattern hits the interpreter
nested-field decay landmine; the `rel_*` family uses PLAIN module functions
(no fn-field registry), so struct-typed observation inputs are safe — and the
detail design additionally unpacks `RelBlockObs` into scalars at the FTL
decision fns as belt-and-braces.

---

## 1. Module decomposition — the `rel_*` family

A new pure-policy family sits **below `fil`** in the import graph: each module
does `use nvme_types.*` only (like `fil_ecc`, `fil_badblock`, `hooks`), so both
`fil.spl` (device-near actuation) and `ftl.spl` (mapping-aware scheduling) may
import it without creating a cycle (inventory C: `ftl` imports `fil`; `fil` never
imports `ftl`; both share the `nvme_types` leaf).

| Module | Role | Taxonomy anchor (scope) |
|---|---|---|
| `rel_types.spl` | ALL shared structs/enums: observation structs, the `RelAction` verdict enum, per-policy state structs, and the two mount bundles. Owned leaf, mirrors `nand_types.spl`'s role for the emu. | — |
| `rel_ladder.spl` | Recovery-ladder state machine (pure). One `rel_ladder_step` advances the taxonomy §1 escalation: hard read → Vref retry → parity → quarantine. | §1 ladder |
| `rel_vref.spl` | Fixed retry table (§2.1) + per-block calibrated-offset cache (ROR-lite, §2.2). SLC hard-decision only. | ROR / §2.1, §2.2 |
| `rel_refresh.spl` | Refresh-scheduling decision fns: fixed-interval + error-aware. FCR-lite / DEAR-lite, §3.3. | FCR, DEAR / §3.3 |
| `rel_disturb.spl` | Read-disturb stress counters + reclaim thresholds. STRAW-lite (block-granular in v1; per-wordline is v2), §3.4. | STRAW / §3.4 |
| `rel_wear.spl` | Static-WL scheduling with dwell/recovery deferral. SREA-lite, §3.7. | SREA / §3.7 |
| `rel_health.spl` | Corrected-bit / RBER bookkeeping + retry-depth + refresh-cause counters. Feeds every other policy and observability. | §3.11 features |

Naming: all public types prefix `Rel` (interpreter global-registry collision
guard, same rule as the emu's `Ne` prefix). Constant tables are `fn`-returning
literals, not module-level collection initializers (freestanding-safe, matches
the `nand_emu` convention).

### Mount bundles (pure state, composed by the layer)

The mounts are **not** new handle-holding modules — that would cycle back into
`fil`/`ftl`. Each mount is a plain state struct in `rel_types` that the layer
**composes as a field**; the actuation loop lives at the layer, which owns the
handle:

- `RelFilMount { vref: RelVrefCache, health: RelHealth, ladder: RelLadderState }`
  — composed into the FIL read path.
- `RelFtlMount { refresh: RelRefreshState, disturb: RelDisturbState, wear: RelWearState, health: RelHealth }`
  — composed into the FTL maintenance tick.

```
<!-- sdn-diagram:id=rel_module_mount -->
                        ┌───────────────────────── FTL layer (owns Ftl handle) ─────────────────────────┐
                        │  ftl maintenance_tick  ──drives──►  RelFtlMount {refresh,disturb,wear,health}  │
                        └───────────────┬──────────────────────────────┬────────────────────────────────┘
                                        │ imports (mapping-aware)       │
   ┌──────────────── FIL layer (owns Fil handle) ────────────┐         │
   │  fil.read (ECC-FAIL branch) ─drives─► RelFilMount        │         │
   │                              {vref, health, ladder}      │         │
   └───────────────┬─────────────────────────────────────────┘         │
                   │ imports (device-near)                              │
   ┌───────────────▼────────────────────────────────────────────────────▼───────────────┐
   │  rel_* PURE FAMILY  (use nvme_types.* only — NO Fil/Ftl handle, verdict-returning)   │
   │  rel_ladder · rel_vref · rel_refresh · rel_disturb · rel_wear · rel_health           │
   │  rel_types (RelAction verdict enum · observation structs · policy state · mounts)    │
   └──────────────────────────────────────────────┬──────────────────────────────────────┘
                                                   │ use
                                          ┌────────▼────────┐
                                          │   nvme_types    │  (constants/opcodes leaf)
                                          └─────────────────┘
```

---

## 2. Mount model and placement

Each policy is a set of **pure decision functions** over a narrow observation
struct, returning a `RelAction`. Mounting is done by two thin adapters:

- **FIL mount (device-near).** Inside the FIL read path. On a read it can re-sense
  at a shifted reference (`set_vref_offset` — note §3: this actuator is
  **chip-global**, `vref = 128 + offset`, not per-block; the per-block calibration
  is *firmware state* the mount applies through the one global knob per read). It
  keys its `RelVrefCache` by **physical block**. It never sees L2P.
- **FTL mount (mapping-aware).** Inside the service tick. It schedules
  refresh / reclaim / static-WL using L2P (`me.map`), logical hotness
  (`hooks.classify_hot`), and GC/band state, and actuates through `reclaim_block`
  / rewrite.

### Placement decision table (two-axis)

Criterion: **decision inputs** — *needs L2P / hotness / GC state? → FTL-pinned;
else placeable.* **Actuation** — *re-sense/calibrate → FIL; reclaim/remap/rewrite
→ FTL.*

| Policy | Decision inputs | Actuation | Default mount | Movable? |
|---|---|---|---|---|
| `rel_ladder` (retry escalation) | physical: ECC code, corrected-bits, retry depth → **placeable** | re-sense at Vref (FIL); escalate verdict to parity/quarantine | **FIL** | Yes → FTL over a `read_raw`, but every read site must opt in (see below) |
| `rel_vref` (ROR-lite calibration) | physical: winning offset per block → **placeable** | apply global Vref + cache (FIL) | **FIL** | Yes, with the ladder |
| `rel_refresh` (FCR/DEAR-lite) | physical: age(seq), corrected-bit trend → **placeable** decision | rewrite to fresh block → **FTL** (needs map) | **FTL** | Decision placeable; actuation FTL-pinned |
| `rel_disturb` (STRAW-lite) | physical: per-block read count → **placeable** decision | `ReclaimNow` → **FTL** | **FTL** | Decision placeable; actuation FTL-pinned |
| `rel_wear` (SREA-lite static WL) | physical: erase spread, dwell → **placeable** decision; but victim selection wants cold/hot → borderline | reclaim coldest → **FTL** | **FTL** | Decision placeable; actuation FTL-pinned |
| hot/cold data separation | **logical hotness (L2P)** → **FTL-pinned** | write-path placement → FTL | **FTL** | No — decision itself needs L2P |
| RAIN reconstruction (existing) | physical stripe geometry | erase+reprogram → FTL | **FTL** | No |

**Ladder default = FIL, with an honest cost.** Mounting the ladder at the FIL
read seam means *every* internal `me.fil.read` inherits retry transparently —
including the GC-relocate read, the scrub read, the RAIN-rebuild read, and the
`reclaim_block` source read that today aborts immediately on `NAND_ECC_FAIL`
(inventory A1/A2; `ftl.spl:520-522`). Moving the ladder up to FTL would require
every read site to opt in explicitly and re-plumb a raw-sense primitive — that is
the price of "FIL thin". The architecture therefore **recommends FIL** but the
table keeps it movable to honor the LAW.

---

## 3. Actuation seam — verdict-driven

Policies return `RelAction`; the mounting layer executes it with its own handle.
Verdict variants (in `rel_types`):

- `Accept` — data good / no action.
- `RetryAtOffset(offset)` — FIL mount: set global Vref, re-sense, re-observe.
- `CalibrateBlock(blk)` — FIL mount: persist the winning offset into `RelVrefCache`
  (ROR: learn the block's optimal reference).
- `MarkForRefresh(blk)` — FTL mount: enqueue an age/error-driven rewrite (FCR/DEAR).
- `ReclaimNow(blk)` — FTL mount: `reclaim_block` (disturb/wear/read-repair).
- `Quarantine(blk)` — FTL mount: retire + `alloc_spare` remap.
- `Uncorrectable` — ladder exhausted; surface `NAND_ECC_FAIL` to the host
  (last rung of taxonomy §1).

**Interpreter note (detail-design gate):** `RelAction` is an
enum-with-payload; the inventory warns cross-module tuple/struct returns can decay
under the interpreter. Detail design must confirm payload round-trips across the
`rel_ladder` → mount boundary; if it does not, fall back to an identically-shaped
tagged struct `RelAction { kind: i64, arg: i64 }` (no interface change to callers).

### NAND_ECC_FAIL read path, rewired

Current behavior (inventory A1/A2): the first `NAND_ECC_FAIL` fails immediately;
the `set_vref_offset` actuator is wired end-to-end but has **no** firmware caller.
Rewired through `rel_ladder` (chip-global Vref actuation shown explicitly):

```
<!-- sdn-diagram:id=ecc_fail_ladder -->
Host        Ftl.read      Fil.read/RelFilMount     rel_ladder(pure)   rel_vref     rel_health     RAIN
 │  read(lba)  │                  │                      │               │             │            │
 │────────────►│  fil.read(ppn)   │                      │               │             │            │
 │             │─────────────────►│ ecc_decode → FAIL    │               │             │            │
 │             │                  │ obs0{FAIL,bits,d=0}  │               │             │            │
 │             │                  │─────────────────────►│ step          │             │            │
 │             │                  │  seed offset ◄───────┼───────────────│ lookup(blk) │            │
 │             │                  │◄─────────────────────│ RetryAtOffset(k0)           │            │
 │             │  set_vref(k0) [GLOBAL knob]             │               │             │            │
 │             │  read_at_vref(ppn,k0) → obs1{bits,d=1}  │               │             │            │
 │             │                  │─────────────────────►│ step (table/valley sweep)   │            │
 │             │                  │◄─────────────────────│ RetryAtOffset(k1) … until OK/FIXED       │
 │             │  on FIXED/OK:     │                      │               │             │            │
 │             │                  │──── CalibrateBlock ──►│──────────────►│ calibrate(blk,kW)        │
 │             │                  │──── observe(bits,depth) ─────────────►│ record    │             │
 │             │  restore vref=0   │                      │               │             │            │
 │◄────────────│  good data (+ MarkForRefresh(blk) if bits high → FTL mount)           │            │
 │             │                  │                      │               │             │            │
 │  (if table exhausted) ladder → Uncorrectable ─► mount escalates to parity ─────────►│ reconstruct│
 │             │                  │  parity fail ─► Quarantine(blk) ─► alloc_spare; NAND_ECC_FAIL→host│
```

The FIL mount owns the `Fil` handle and the loop; `rel_ladder`/`rel_vref`/
`rel_health` stay pure. Because the loop lives at `fil.read`, the
`reclaim_block` source read (`ftl.spl:520`) stops being a hard abort — it retries
first, closing gap A2 for free on the GC/scrub/RAIN internal-read paths.

### Prerequisite seams (detail-design; `fil.spl`/`fil_nand_emu` unmodifiable here)

The ladder and observability need three thin extensions that do not exist yet:

1. **Corrected-error signal on reads.** `FilRead {data,lba,seq,code}` does not
   surface the ECC decode outcome as an observable. Two honest constraints
   (cross-review 2026-07-19): `ecc_decode` knows only a coarse tri-state
   (clean / corrected / uncorrectable), NOT a per-bit count; and its numeric
   input (`injected_flips`) is fault-injection-only — the read path never
   derives it from real Vt physics, so genuine drift surfaces only as
   parity-mismatch FAIL. The seam therefore has two parts: (a) add a
   `corrected: i64` field carrying the coarse bucket (0/1/2+); (b) make the
   NandEmu backend derive its error count from physics — a written-word shadow
   per ppn, `err = popcount(sensed XOR shadow)` — which MODELS the corrected-bit
   telemetry a real decoder reports and makes the corrected bucket reachable
   from genuine retention/disturb drift. Without (b), refresh policies keyed on
   corrected events are only fault-injection-testable.
2. **Explicit-Vref sense primitive.** No `fil.read_at_vref(ppn, offset)` /
   `read_raw` exists to sense at a chosen reference without ECC-fail being
   terminal. The ladder loop requires it.
3. **Emu soft-observability re-export.** `vt_histogram(page)` / `read_margin(page)`
   exist on `NeChip` but are **not** re-exported through the `NandEmu` wrapper
   (inventory B1/B3) — specs cannot see them. Add passthroughs for validation
   (§5).

---

## 4. Wiring plan — the four unwired mechanisms

Four mechanisms are implemented but have **zero production callers** (inventory
A3/A5/A6/A7): `scrub_once`, `wear_level_once`, `rain_seal`, `alloc_spare`. They
are wired into the FTL maintenance tick, mirroring the existing convention: *at
most one background GC step per service iteration when free space is below the
low watermark* (`nvme_controller.spl:479-485`).

**Budget invariant (critical).** `gc_once`, `scrub_once`, `wear_level_once`, and a
refresh rewrite **all drain into the shared `GC_RESERVE` (2 blocks)** via
`reclaim_block`. Firing several per tick can exhaust the reserve and make later
ones abort (fail-closed `UNMAP` — no data loss, but thrash). So the faithful
extension is **one reclaim-class step per tick, total**, chosen by a fixed
priority among gated candidates:

| Order | Step | Gate (watermark/threshold) | Class |
|---|---|---|---|
| 1 | `gc_once` | `free_blocks() < GC_LOW_WATERMARK` | reclaim (shared slot) |
| 2 | refresh rewrite (`MarkForRefresh` queue) | `rel_refresh_due` fired (age/error) | reclaim (shared slot) |
| 3 | `scrub_once` | any block `rd_disturb > READ_DISTURB_THRESHOLD` | reclaim (shared slot) |
| 4 | `wear_level_once` | `max_erase - min_erase > WL_THRESHOLD` | reclaim (shared slot) |
| — | `rain_seal` | parity dirty | parity-only → **own** bound, ≤1 stripe/tick |
| — | `alloc_spare` | **event-driven** from the retire path (`Quarantine` / program-fail / erase-fail) | not in round-robin |

`rain_seal` relocates no host data (parity only), so it takes its own small
per-tick bound and does not compete for the reclaim slot. `alloc_spare` is not a
background step at all — it fires from bad-block retirement (`fil.mark_bad` →
`band.set_bad`) to remap a retired block onto a reserved OP spare (blocks 56..63,
`fil_badblock.spl`), closing gap A7. Not power-safe items (RAIN, `rain_seal`)
keep their existing honesty note.

---

## 5. Observability

`rel_health` is the single sink and the validation surface.

**Records (per block unless noted):**
- Corrected-error events per read — the coarse `FilRead.corrected` bucket
  (0 clean / 1 corrected / 2+ uncorrectable, §3 prereq 1). With the NandEmu
  shadow-word seam (§3 prereq 1b) the emu backend's bucket reflects a modeled
  per-read bit count; on backends without it, treat as an event flag only.
- RBER estimate — corrected-error EVENTS ÷ reads over a window
  (`rel_health_rber(blk)`); a modeled bits-per-read rate only where prereq 1b
  is present. Name the distinction in specs — do not present event-rate as
  true bit-RBER.
- Retry depth reached — how many ladder rungs a read needed (0 = clean).
- Refresh cause tags — age (FCR) vs. error trend (DEAR) vs. disturb (STRAW), so a
  spec can assert *why* a rewrite fired.

**Validation against the emulator (this is why the emu exists).** The `nand_emu`
Vt model is the oracle. Specs drive absolute, observable outcomes:
- Inject retention drift (`emu_advance_time_s` + `set_block_wear`) → `read_margin`
  narrows → a plain read surfaces `NAND_ECC_FAIL` → the ladder's `RetryAtOffset`
  sweep finds a winning offset → `vt_histogram` confirms the valley moved →
  `CalibrateBlock` restores a clean read on the next access (ROR-lite proven).
- Read-disturb: bump `rd_disturb` past threshold → `rel_disturb_due` →
  `ReclaimNow` → post-reclaim `read_margin` recovers (STRAW-lite proven).

**Prerequisite (blocks §5 specs):** `vt_histogram`/`read_margin` are chip-level
and **not re-exported** through the `NandEmu` wrapper (inventory B1/B3). Detail
design must add wrapper passthroughs (and FIL/FTL test accessors) before these
specs can assert on soft margins — the same "re-export the observable" gap the
retry ladder's corrected-bit seam has.

---

## 6. v1 / v2 scoping

v1 = validatable **today** on the SLC, hard-decision, single-plane emu. v2 = needs
the emulator to grow before the algorithm's effect is observable (mark honestly;
never fake).

| Capability | v1 (SLC-validatable) | v2 (needs emu growth) |
|---|---|---|
| Retry ladder (`rel_ladder`, §1/§2.1) | ✅ hard-decision Vref sweep | — |
| ROR-lite per-block calibration (`rel_vref`, §2.2) | ✅ global Vref knob + per-block cache | ReMAR/HeatWatch age+temp models |
| FCR/DEAR-lite refresh (`rel_refresh`, §3.3) | ✅ seq-age + corrected-bit trigger | temperature-triggered refresh (no temp model) |
| STRAW-lite disturb reclaim (`rel_disturb`, §3.4) | ✅ block-granular counters | per-wordline STRAW (no wordline model) |
| SREA-lite static WL (`rel_wear`, §3.7) | ✅ erase-spread + dwell deferral | self-recovery physics (dwell model is phenomenological) |
| `rel_health` RBER bookkeeping (§3.11) | ✅ corrected-bit/retry-depth counters | ML predictors |
| Wiring pass (§4) | ✅ scrub/WL/rain_seal/alloc_spare into tick | — |
| Soft-decision LDPC / VaLLR LLR (§2.4/§2.5) | ❌ | multi-read soft channel + LDPC; emu is 1 bit/cell |
| LaVAR per-layer calibration (§2.3) | ❌ | 3D layer variation model |
| ReNAC neighbor-assisted (§2.6) | ❌ | inter-cell coupling model |
| MGC/STAR/ColdCode state-mapping (§3.6) | ❌ | multi-level state distributions |
| CellRejuvo / cell-mode downgrade (§2.10/§3.9) | ❌ | charge-state manipulation / MLC modes |

The trade-off is the taxonomy's (§6): every recovery/refresh step lowers UBER at
the cost of reads, writes, latency, and endurance — the budget bound in §4 is the
architecture's answer to it.

**Coverage of gap-analysis ranked items not named as `rel_*` modules
(cross-review 2026-07-19):** opportunity #8 (error/age-aware GC victim
scoring) is deliberately NOT a new module — it lands as an extension of the
existing `hooks.gc_score` default scorer, fed by `rel_health` observations;
opportunity #10 (RFR/RDR-lite failure-mode classification) folds into
`rel_health`'s cause-tagging in v1 (classification only) with probabilistic
bit-flip recovery deferred to v2. The placement table's RAIN row describes the
PRE-EXISTING `rain.spl` mechanism as-is (marked "(existing)"), so it does not
carry the decision/actuation split applied to new `rel_*` rows.

---

## 7. Non-goals (anti-over-engineering)

The whole architecture is *the `rel_*` module family + two composed mount
bundles + the verdict enum*. Explicitly **not** built: no speculative plugin
registry, no config-file policy DSL, no per-policy dynamic loader (the `hooks`
sandbox already covers runtime-installable *scoring*; reliability actuation is
static firmware). Composition only, no inheritance, no dead flexibility.
