# NVMe Firmware — MDSOC+ Layer Architecture (host / FTL / NAND)

**Date:** 2026-09-01
**Status:** Plan — workstream B of the spine
**Spine:** `doc/03_plan/hardware/nvme_complete_fw_mdsoc_offload_master_plan.md` §3 (lines 91-124), artifact row `:208`
**Enforcement spec this doc must not contradict:** `nvme_ssd_firmware_hardening_design_plan.md` §13
**Subject tree:** `examples/09_embedded/simpleos_nvme_fw/fw/` — 76 entries: **72 `.spl`** (14,686 lines), 4 `.md`, plus `proofs/`. Of the 72: 30 are `*_check.spl`, 4 are harness, **38 are production modules**.

---

## 0. Goal

Express the firmware as three MDSOC dimensions (host / FTL / NAND) with an ECS
business layer in the two userland-class dimensions, cross-cutting concerns as
woven aspects rather than inline calls, and cross-dimension access denied by
enforcement rather than convention. Nothing below describes what exists today.

## 1. Current state vs target state — a real conflict, adjudicated

This is not a contradiction to resolve by picking a side; it is current-state
versus target-state, and the two sources say different things on purpose.

| Source | Claim |
|---|---|
| `fw/CONVENTIONS.md:8-12` | "**MDSOC-only (driver tier).** … **no ECS** — `use std.ecs` is forbidden for drivers per the architecture Layer Rules" |
| `fw/README.md:75-86` | The whole tree is MDSOC-only; "MDSOC+" in req 4 means the research's *multi-domain* sense, not `MDSOC outer + ECS inner`; `grep -r "use std.ecs" fw/` returns nothing |
| Spine `§3:91-124` | "SSD firmware spans both, so the split is explicit" — HOST and FTL are **MDSOC + ECS**; NAND is **MDSOC-only** |

**The spine is the controlling target.** It knowingly re-adjudicates the tree's
own blanket driver-tier classification: an SSD's host and FTL dimensions are
not driver-class work, they are userland-class services that happen to be
compiled into firmware. CLAUDE.md's rule ("MDSOC outer + ECS business layer for
userland services/apps; kernel/drivers stay MDSOC-only") is therefore applied
*per dimension*, not per artifact.

**Consequence, and it is a migration step, not a footnote:** this plan is
invalid while `fw/CONVENTIONS.md:8-12` and `fw/README.md:75-86` still forbid
what it prescribes. Phase 0 below rewrites both to scope "MDSOC-only, ECS
forbidden" to the NAND dimension. Those files are *not* edited by this
document.

## 2. Dimension assignment of the existing tree

Derived from the actual import graph (`use` lines, measured 2026-09-01). "Straddles"
= the refactor targets.

### 2.1 HOST dimension (target: MDSOC + ECS)
PCIe/NVMe transport, queues, doorbells, PRP/SGL, DMA, decode/validate,
completion, SMART/Identify/log.

| File | Lines | Note |
|---|---|---|
| `fw/nvme_qset.spl` | 665 | queue set; imports `hil_queue` only for `bool_to_i64` (`:22`) — a utility leak, not a real edge |
| `fw/nvme_admin.spl` | 633 | Identify/log/features |
| `fw/hil_queue.spl` | 397 | SQ/CQ rings |
| `fw/hil_command.spl` | 189 | command decode |
| `fw/nvme_main.spl` | 172 | entry |
| `fw/nvme_admin_types.spl` | 114 | leaf types |
| `fw/dram.spl` | 251 | host-visible buffer memory |
| `fw/fw_pool.spl` | 316 | command/task pool |
| `fw/power_thermal.spl` | 196 | imports `nvme_admin_types` (`:16`) for feature IDs — clean |
| `fw/hil.spl` | 268 | HIL facade. Imports `ftl.*` (`:16`) — this is the **legal downward port edge**, the one HOST→FTL dependency the rules in §6.1 `allow`; it becomes `port/host_ftl` in Phase 4 |
| `fw/nvme_controller.spl` | 1193 | see S2 |
| `fw/firmware.spl` | 275 | top-level cooperative reactor `Firmware{hil{ftl{fil}}}` (`:10`). Spans all three by composition — it is the **composition root**, which is legitimately dimension-crossing; it stays outside the sealing rules and is the only module allowed to name more than one dimension |

### 2.2 FTL dimension (target: MDSOC + ECS)
Mapping, journal, bands, GC, wear, recovery, QoS.

| File | Lines |
|---|---|
| `fw/ftl.spl` | 1095 |
| `fw/ftl_band.spl` | 438 |
| `fw/ftl_map.spl` | 371 |
| `fw/ftl_journal.spl` | 274 |
| `fw/ftl_gc.spl` | 61 |
| `fw/rain.spl` | 147 |
| `fw/rel_types.spl` `rel_health` `rel_refresh` `rel_disturb` `rel_wear` `rel_ladder` `rel_vref` | 157/127/142/122/71/135/113 |
| `fw/hooks.spl` `fw/sandbox.spl` | 255/89 — policy-hook registry + sandbox |

### 2.3 NAND dimension (MDSOC-only, driver class)
FIL scheduler, ECC, retry ladder, bad block, channel/way, controller registers,
ONFI sequencing.

| File | Lines |
|---|---|
| `fw/fil.spl` | 374 |
| `fw/fil_fmc.spl` | 326 — flash-memory-controller register driver |
| `fw/fil_nand_device.spl` | 444 — ONFI handshake |
| `fw/fil_nand_emu.spl` | 456 — Vt-physics backend |
| `fw/fil_nand.spl` `fil_ecc.spl` `fil_scheduler.spl` `fil_badblock.spl` | 259/203/183/122 |
| `fw/nd_types.spl` | 150 |

### 2.3b Harness and check tier — outside all three dimensions

Each of the 30 `*_check.spl` files takes **the dimension of its subject module**
(`ftl_map_check`→FTL, `fil_nand_emu_check`→NAND, `host_transport_check`→HOST,
and so on) and is bound by the same sealing rules within that dimension.

The 4 harness modules — `sim_main.spl` (118), `test_fw.spl` (77),
`fw_layer_smoke.spl` (47), `nand_migration_capture_main.spl` (63) — are
**harness-tier: outside all three dimensions**, exempt from the sealing rules
(they legitimately reach across), and **excluded from the production link**
per §13.7's "no test/emulator object files in link inputs". They are not
forgotten; their exclusion is itself an enforcement obligation.

### 2.4 Straddlers — the refactor targets

| # | File:line | Straddle | Fix |
|---|---|---|---|
| S1 | `fw/nvme_types.spl` (150) | The "frozen shared interface" every one of the 73 files imports. It carries host command shape (`:95-98`, incl. `data: i64 # simulated single-byte payload stand-in`) **and** media geometry constants together. Single largest cross-dimension coupler. | Split into `host_types` / `ftl_types` / `nand_types` — **last**, see §6 |
| S2 | `fw/nvme_controller.spl:24-27` (1193) | Host controller imports `ftl.*`, `power_thermal.*`, `dram.*`, `openssd_config.*` directly, reaching past HIL into the FTL dimension | Route through the HOST↔FTL port; controller sees typed block ops only |
| S3 | `fw/openssd_config.spl:9` | Host/platform config imports `fil_scheduler.*` for NAND channel geometry | Geometry becomes a NAND-published capability record, not an import |
| S4 | `fw/rain.spl:15` | FTL RAIN imports `fil_scheduler.*` for `NUM_CHANNELS`, `sched_fill` — FTL consuming NAND channel topology | Same as S3. This is the leak §4's rules must catch |
| S5 | `fw/fil.spl:14-16` | NAND FIL imports `rel_types` / `rel_vref` / `rel_ladder` — reliability policy is FTL-class, sitting inside the driver dimension | Either reclassify the `rel_*` ladder as NAND-owned (defensible: it is a retry state machine over sense operations) or invert to a callback. **Decide before Phase 3** |
| S6 | `fw/ftl.spl:20-21` | FTL imports `sandbox` + `hooks` — correct, but the hook registry is dimension-agnostic and should be a shared aspect substrate, not an FTL import |
| S7 | `fil_nand_device.spl:299-309`, `fil_nand_emu.spl:334-405` | `inject_prog_fail` / `inject_erase_fail` / `inject_read_bitflip` / `inject` are **methods on production structs** — test control living in shipping objects | Becomes an aspect. §3 |
| S8 | `fw/hil.spl:16`, `fw/firmware.spl:10` | Composition chain `Firmware{hil{ftl{fil}}}` hardwires the stack by construction | Keep the composition; add named ports so the edge is nameable by a pointcut |

## 3. ECS entity model

Applied only in HOST and FTL. Components are plain data; systems are the
existing module functions, re-expressed as system passes over component arrays.
This preserves value semantics and the COW discipline (`.claude/rules/code-style.md`).

### 3.1 HOST entities
| Entity | Components | Systems | Backed today by |
|---|---|---|---|
| `Command` | `CmdHeader{cid,opcode,nsid}`, `Lba{lba,nblocks}`, `Payload`, `CmdState`, `CompletionSlot` | decode, validate, dispatch, complete | `hil_command.spl` (189), `nvme_types.spl:95-98` |
| `Queue` | `RingGeom{depth,base}`, `HeadTail`, `Doorbell`, `QueuePolicy` | drain, backpressure, tail-advance | `hil_queue.spl` (397), `nvme_qset.spl` (665) |
| `Namespace` | `NsGeom{lba_size,capacity}`, `NsFormat`, `NsHealth` | identify, format, delete | `nvme_admin.spl` (633) |
| `DmaLease` | `HostRange`, `DeviceBuf`, `Direction`, `LeaseState` | acquire, map, release | `dram.spl` (251), `fw_pool.spl` (316) |

`DmaLease` as a first-class entity is what makes §13.7's "no relocations to
forbidden regions" checkable — the lease is the only legal way host memory is
named.

### 3.2 FTL entities
| Entity | Components | Systems | Backed today by |
|---|---|---|---|
| `MappingTxn` | `LbaKey`, `PpnValue`, `TxnState`, `JournalSeq` | lookup, update, commit, rollback | `ftl_map.spl` (371) |
| `Band` | `BandId`, `BandState{FREE/OPEN/CLOSED/BAD}`, `ValidCount`, `EraseCount` | allocate, close, reclaim | `ftl_band.spl` (438) |
| `JournalRecord` | `Seq`, `RecKind`, `Payload`, `Durable` | append, checkpoint, replay | `ftl_journal.spl` (274) |
| `GcTask` | `VictimBand`, `Progress`, `ReclaimBudget`, `Priority` | select, migrate, reclaim | `ftl_gc.spl` (61), `ftl.spl` |
| `RelObs` (added) | `RelHealth`, `RelAction`, `RetryDepth`, `Corrected` | refresh, scrub, wear-level | `rel_*` (~867 total) |

Budget note: `hooks.spl:~230` documents that `gc_once`, refresh rewrite,
`scrub_once` and `wear_level_once` all drain a shared `GC_RESERVE` via
`reclaim_block`. In ECS terms that is one `ReclaimBudget` resource contended by
four systems — making it an explicit component is the point, not a side effect.

### 3.3 NAND — no ECS
`NandOp`, `Channel`, `Block` are named in the spine but stay **plain MDSOC
structs**, not entities. See §5.

## 4. Aspects — concerns that stop being inline calls

Cross-cutting concerns currently written as calls inside business logic move to
declared aspects woven at build time (spine `:118-120`).

| Concern | Today | As an aspect | Advice form |
|---|---|---|---|
| Logging | ad-hoc, per module | `on pc{ execution(* ftl_*(..)) } use log_advice before` | `before` — compile-time |
| Tracing | absent | boundary-only: HOST↔FTL and FTL↔NAND ports | `before`/`after_success` — compile-time |
| Telemetry | `hooks.spl` `telemetry(kind,code,value,fuel)` hook | `after_success` on port functions, feeding the same registry | compile-time |
| Timing / fuel | inline `fuel_used` accounting in `hooks.spl` | `around` on hook invocation | **runtime-woven** |
| **Fault injection** | `inject_*` **methods on production structs** (`fil_nand_device.spl:299-309`, `fil_nand_emu.spl:334-405`); 31 `inject` mentions in `fil_nand_emu.spl`, 25 in `fil_nand_device.spl` | advice on `execution(* nand_read_page(..))` etc., replacing the result | **`around`** |

**Why fault-injection-as-aspect is the load-bearing one.** It is how test
control stops being a method on a production object. Once `inject_read_bitflip`
is advice rather than a method, §13.7's "no exported test hooks" and "no
`.fault_model` / `.test_control` sections" become *mechanically* checkable: the
production link simply does not weave the aspect, so the symbol is absent
rather than present-but-unused.

**Honest dependency:** replacing a call's return value requires `around`, and
`aop.md:46` states weaving is "compile-time for `before`/`after`, **runtime for
`around`**". So the fault-injection aspect carries a runtime-weaving dependency
today, and `aop.md:44` requires `proceed()` exactly once. A firmware image that
must contain *no* injection machinery therefore needs compile-time `around`, or
a build-time source-level variant selection. This is a gap, not a solved
problem — do not plan as if it were compile-time.

## 5. NAND is MDSOC-only — justified, with the boundary challenged

**Justified.** `fw/README.md:81` gives the rationale in the tree's own words:
"drivers are IO-bound state machines, not entity graphs." The NAND dimension is
ONFI/Toggle sequencing, register writes, an ECC codec, and a retry ladder.
Its state is a fixed hardware topology (`NUM_CHANNELS` ways × blocks × pages),
known at build time, with no dynamic population and no need for per-entity
component addition. An ECS over it would buy archetype flexibility nothing
needs and cost indirection on the hottest path. It is also the dimension most
likely to be replaced by RTL under the movable software/circuit boundary
(spine `:75-80`) — plain structs lower to hardware; entity graphs do not.

**Challenged: the boundary placement, not the rule.**
1. **S4/S3 are live violations of the rule you are agreeing to.** `rain.spl:15`
   and `openssd_config.spl:9` import `fil_scheduler` for `NUM_CHANNELS`. If NAND
   is a sealed driver dimension, its channel topology cannot be an import target
   for FTL and host config. It must be a published capability record crossing the
   port. The rule is right; the tree does not obey it.
2. **S5 puts FTL-class policy inside the driver.** `fil.spl:14-16` imports
   `rel_types`/`rel_vref`/`rel_ladder`. A retry *ladder* is arguably NAND-owned
   (it sequences senses); a refresh/wear *policy* is not. Split the `rel_*` group
   along that line before Phase 3 rather than letting the ambiguity harden.
3. **`fil_scheduler.spl` (183) is the honest edge case.** Channel/way scheduling
   is queueing over a resource pool — the one place an ECS would not be absurd.
   It stays MDSOC-only for consistency and for RTL-lowerability, and that is a
   trade being made with open eyes.

## 6. Cross-dimension enforcement — today vs deferred

Enforcement must satisfy hardening §13, whose §13.1 requires five layers and
accepts none alone.

### 6.1 Enforceable TODAY
`aop.md:26-27` gives working `forbid`/`allow` over `import(...)` and
`depend(within(...), within(...))`, with `**` globs; `aop.md:199-221` records
forbid- and allow-rule scenarios as **passing**.

```simple
# Dimension sealing — downward only.
forbid pc{ depend(within(nand.**), within(ftl.**)) }
forbid pc{ depend(within(nand.**), within(host.**)) }
forbid pc{ depend(within(ftl.**),  within(host.**)) }

# Host may not name media coordinates; FTL may not name host PRP/DMA.
forbid pc{ import(nand.geometry.**) within(host.**) }
forbid pc{ import(host.dma.**)      within(ftl.**) }

# S3/S4 specifically.
forbid pc{ depend(within(ftl.**),  within(nand.fil_scheduler.**)) }
forbid pc{ depend(within(host.**), within(nand.fil_scheduler.**)) }

# Test control out of production (§13.2).
forbid pc{ import(fault.**) within(prod.**) }

# The one allowed edge per boundary.
allow pc{ depend(within(host.**), within(port.host_ftl.**)) }
allow pc{ depend(within(ftl.**),  within(port.ftl_nand.**)) }
```

Also today: `execution(...)` pointcuts for the logging/tracing/telemetry
aspects (`aop.md:20,23`), compile-time for `before`/`after`.

### 6.2 Deferred — needs pointcuts that do not exist
Measured: a selector census of `doc/02_requirements/language/aop/aop.md` returns
**only** `execution(`, `import(`, `depend(`, `within(` — and a grep for
`pc{ get`, `pc{ set`, `pc{ effect`, `effect(` across `aop.md` and
`src/compiler/85.mdsoc/weaving/` returns **zero hits**. So:

| Needed by | Pointcut | Status |
|---|---|---|
| §13.2 | `call(backends.nand.**::*)` | **`call(` is not in aop.md at all** — only `execution` (callee-side). Callee-side cannot express "only the media service may call this" |
| §13.3 | `mem_read/mem_write(region, type, provenance)` | absent |
| §13.3 | `mmio_read/mmio_write(register, width)` | absent |
| §13.3 | `dma_map` / `dma_descriptor_write` | absent |
| §13.3 | `raw_address_construct` / `raw_pointer_cast` | absent |
| §13.3 | `ffi_call(symbol, declared_effect_set)`, `inline_asm(effect_set)` | absent |
| §13.4 | effect declarations + inference | absent |
| §13.5 | region provenance | absent |
| §13.7 | link/section/relocation verification | not an AOP feature; a separate post-link checker |

**Honest statement of reach.** Of §13.1's five proof layers, only layer 1
(dependency/import policy) is reachable today, and only in its *import/depend*
half — not its `call` half. Layers 2-5 are unbuilt, matching the spine's own
"it is unbuilt" (`:124`). Field get/set and effect pointcuts are genuinely
absent from the requirement document, not merely unimplemented; they must be
specified before they can be deferred to.

**Interim substitute, so Phase 1 is not vacuous:** a fail-closed shell gate
in `scripts/check/` over the `use` graph of `fw/`, with the §13.9 negative
corpus as fixtures — each forbidden edge gets a fixture that must FAIL, and
the gate is ERROR (not PASS) when it inspects 0 files, per this repo's verdict
convention.

## 7. Migration order — 9 phases (0-8), tree never broken at once

The ordering rule: **additive first, subtractive last.** `nvme_types.spl` is
imported by all 73 files; splitting it first breaks everything simultaneously,
so it is Phase 7, not Phase 1.

| Phase | Action | Files touched | Breaks build? |
|---|---|---|---|
| **0** | Rewrite `fw/CONVENTIONS.md:8-12` + `fw/README.md:75-86` to scope "MDSOC-only / no ECS" to the **NAND** dimension only. Without this the tree's own rules forbid Phases 4-6. | 2 docs | no |
| **1** | Add the dependency gate in **report-only** mode + §13.9 negative fixtures. Records the S1-S8 violations as a baseline; ratchets, does not block. | +1 script, +fixtures | no |
| **2** | Introduce named ports `port/host_ftl.spl`, `port/ftl_nand.spl` as **additive** typed interfaces. Nothing migrates to them yet. | +2 | no |
| **3** | Resolve **S5** (`fil.spl:14-16` `rel_*` split) and **S3/S4** (publish NAND geometry as a capability record; delete `fil_scheduler` imports from `rain.spl:15`, `openssd_config.spl:9`). Smallest blast radius of the real leaks. | ~5 | one gate flip |
| **4** | Move **S2**: `nvme_controller.spl:24-27` stops importing `ftl`/`dram`/`power_thermal` directly, routes via `port/host_ftl`. Largest single file (1193 lines) — do it alone. | 1 + port | no |
| **5** | Aspects: extract logging/tracing/telemetry to `before`/`after` advice on port functions (compile-time, safe). | ~10 | no |
| **6** | Aspect-ify **S7** fault injection (`fil_nand_device.spl:299-309`, `fil_nand_emu.spl:334-405`) — gated on the `around` weaving question in §4. If unresolved, hold at a build-time variant split and record the block. | 2-3 | no |
| **7** | ECS in **HOST** (§3.1), then **FTL** (§3.2) — separately, HOST first (fewer, smaller files than `ftl.spl`'s 1095). | ~9, then ~14 | no |
| **8** | Split **S1** `nvme_types.spl` into `host_types`/`ftl_types`/`nand_types`. Mechanical once every consumer already sits in a dimension. Flip the Phase-1 gate to fail-closed. | all 73 | yes, once, deliberately |

**Gate discipline:** the Phase-1 gate stays report-only through Phase 7 and
becomes fail-closed only at Phase 8. A ratchet that blocks before the tree can
comply gets routed around, which protects nothing.

## 8. Open items (not resolved by this document)

1. Compile-time `around` weaving — blocks Phase 6's strongest form (§4).
2. `call(...)` pointcut absent from `aop.md` — blocks §13.2 verbatim (§6.2).
3. `rel_*` ownership split, NAND vs FTL — decide before Phase 3 (§5, S5).
4. `nvme_types.spl:98` `data: i64` payload stand-in — the G1 payload gap; it
   sits inside S1 and should be fixed in the same Phase-8 edit.
