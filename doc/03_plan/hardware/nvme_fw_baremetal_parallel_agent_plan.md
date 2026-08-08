# Parallel-Agent Build Plan — SimpleOS NVMe FW Baremetal Example

> **Status (2026-06-29): largely IMPLEMENTED — see `examples/09_embedded/simpleos_nvme_fw/fw/`
> and the operator guide `doc/07_guide/hardware/nvme_firmware/`.** The data-path phases are
> built and run-green (300 self-test assertions): sim NAND, generation-handle pool (`fw_pool`),
> bounded queue (`hil_queue`), cooperative reactor (`firmware.service`), page-level FTL (`ftl`),
> WAL + checkpoint + A/B superblock (`ftl_journal`), P2L crash recovery (`ftl.recover`), GC
> (`ftl_gc`/`ftl.gc_once`), DFTL map cache (`ftl_map`). **Done ≈ phases 0–7.** An NVMe admin +
> multi-IO-queue controller front end (`nvme_admin`/`nvme_qset`/`nvme_controller`/`nvme_main`,
> verified by `nvme_main.spl`) also landed — it is **not** in the phase table below. **Still
> genuinely future:** phase 8 multicore/shard, phase 9 offload/caps, phase 10 dynamic
> hooks/sandbox, and rv32 bare-metal boot. Two scheduled items were **never produced as planned**:
> (a) the Phase-11 "docs" row's generated `doc/06_spec` manual + a `doc/07_guide` guide — the
> guide now exists (link above) but `doc/06_spec` is unmade (no sspec tests exist; the example
> self-verifies via run-mains); (b) the Lean4 proofs A–I were scheduled under the *firmware*
> roadmap but actually landed under `emu/proofs/` (4 files, 20 theorems) verifying the
> **emulator's** algorithms — the firmware itself still has zero Lean. The text below is the
> original plan, kept for the decomposition/process; treat phases 0–7 as done.

> **Scope.** How to build the bare-metal NVMe SSD firmware example (rooted at
> `examples/09_embedded/simpleos_nvme_fw/`) with a fleet of lower-cost worker agents
> (Claude Haiku + Sonnet) gated by Claude Opus reviews, following the SPipe
> research → spec → implement → verify process.
>
> **Sources of truth**
> - Research: [`doc/01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md`](../../01_research/hardware/nvme_firmware/nvme_ssd_firmware_architecture.md) (+ `research_addendum_2026-06-29.md`)
> - This plan: agent decomposition, model tiers, review gates.
> - SPipe lane state: `.spipe/nvme_fw_baremetal/state.md` (goal + acceptance criteria).
> - Working scaffold (Phase 1 slice): `examples/09_embedded/simpleos_nvme_fw/main.spl`.

<!-- sdn-diagram:id=nvme_fw_agent_pipeline -->
```
                       ┌──────────────────────────────────────────┐
   research/addendum → │ Phase L: INTERFACE LOCK (Opus)            │  FROZEN before any fan-out
                       │  shared module/type/fn names + invariants │
                       └───────────────┬──────────────────────────┘
                                       │ (barrier — review + freeze)
        ┌──────────────────────────────┼──────────────────────────────┐
        ▼                              ▼                              ▼
   Haiku workers              Sonnet workers                 Opus verifiers
   (sim/harness/specs/        (pool,queue,runtime,ftl,       (Lean models, recovery
    crash-point gen,          wal,recovery,gc,mapcache,      adversarial verify,
    boilerplate, docs)        offload,nvme,hooks)            review gate per phase)
        └──────────────┬───────────────┴───────────────┬──────────────┘
                       ▼                                ▼
              disjoint file scopes          Opus REVIEW GATE per phase
              (no two agents share a file)  (correctness + false-green audit +
                       │                      invariant check + docs-freshness)
                       ▼
                 merge owner (Opus) → jj commit → next wave
```

---

## 1. Goal

Grow the `simpleos_nvme_fw` example from the Phase-1 minimal slice into the full
"minimal reliable prototype → realistic firmware" path of the research roadmap
(roadmap phases 0–11), using parallel agents whose work is **always reviewed by a
higher-capability model before a done mark, broad exclusion, or release-blocking claim**
(SPipe Cooperative Review rule). Token cost is secondary to correctness and to never
shipping a false-green.

## 2. Model-tier strategy

| Tier | Model | Owns | Task shape | Guardrails |
|------|-------|------|-----------|------------|
| **Worker-A** | **Haiku** | Mechanical, fully-specified, low-ambiguity work | Simulator fixtures, trace/crash-injection harness, repetitive crash-point spec generation, telemetry counters, per-domain boilerplate stubs, doc/manual scaffolding from a frozen interface | One file each; must compile; placeholder helpers `fail("not impl: <name>")`, never silent stubs |
| **Worker-B** | **Sonnet** | Real module implementation against a **frozen** interface | object pool, bounded queue, coroutine runtime, FTL write/read/trim, WAL/checkpoint, P2L recovery, GC, map cache, offload abstraction, NVMe queue/doorbell sim layer, dynamic-hook sandbox | One module (file) each, disjoint scope; must pass `bin/simple check` + its own spec green with **real** assertions |
| **Reviewer** | **Opus** | Architecture, every review gate, formal proofs, final acceptance | Interface-lock pass (Phase L), Lean4 models/proofs, recovery-correctness adversarial verify, per-phase review gate, merge decisions | Reviews are adversarial (try to refute / find false-green); no done mark without an Opus gate pass |

**Why this split.** Haiku is cheapest and reliable on tasks with no design judgement once
the interface is frozen. Sonnet implements well against a clear contract. Opus is reserved
for the irreversible decisions (interfaces, proofs, accept/reject) where a wrong call is
expensive — exactly the SPipe "require a normal/highest-capability review before accepting
done marks" rule.

## 3. The linchpin — Phase L: Interface Lock (Opus, before any fan-out)

The single thing that separates a plan that runs from one that only reads well:
**freeze the shared surface before workers fan out.** One Opus agent produces and an Opus
review accepts a frozen `interfaces.md` defining, for the whole firmware:

- **Module/file names** and their one-line responsibility (the scope each worker owns).
- **Shared type names + field layouts** — `Handle{index,generation}`, `WriteTask`,
  `ReadTask`, `Wal`, `WalRecord{kind,lba,old_ppn,new_ppn,seq}`, `Ftl`, `SimNand`,
  `OffloadOps`, `Checkpoint`, `Superblock`, `BandState`, `MapCacheEntry`, `GcTask`.
- **Function signatures** crossing module boundaries (the only thing workers may call across files).
- **Manual `step("...")` flow helper names** + setup/checker helper names for the SSpec scenarios.
- **The invariant set** (pool/queue/FTL/recovery/multicore — copied from research §13), each
  tagged with the phase that must establish it and whether it gets a Lean proof.
- **Fail-fast placeholders**: every not-yet-built helper is `fail("TODO: <name>")` or
  `assert(false, ...)` — a worker depending on it gets a loud failure, never a silent pass.

Phase L output is reviewed by a second Opus pass and **frozen**. Workers may not rename a
shared symbol; an interface change requires a new Opus interface-lock mini-pass (and a state-file note).

## 4. Phase → agent mapping (disjoint file scopes)

Files live under `examples/09_embedded/simpleos_nvme_fw/` unless noted. **No two agents in a
wave touch the same file** (the parallel-scope-partition rule). Specs live under
`test/01_unit/examples/embedded/...` and `test/02_integration/...`; Lean models under
`examples/09_embedded/simpleos_nvme_fw/proofs/`.

| Roadmap phase | Worker | Disjoint files | Deliverable | Opus review gate |
|---------------|--------|----------------|-------------|------------------|
| 0 Simulator | Haiku | `sim_nand.spl`, `sim_nvme.spl`, `trace.spl` | In-memory NAND (pages+OOB), NVMe SQ/CQ sim, deterministic event/crash trace harness | Trace replay is deterministic; crash injection hits every documented crash point |
| 1 Pool+Queue | Sonnet ×2 | `pool.spl`; `queue.spl` | Generation-handle object pool; bounded FIFO queue | Pool/queue invariants hold; **Lean Phase A/B** proof drafts exist |
| 2 Coroutine runtime | Sonnet | `runtime.spl` | Reactor loop, cooperative `step`, timers, watchdog, cancel/timeout cleanup | No blocking wait; every task has timeout+progress; cancel releases all child handles |
| 3 Page-level FTL | Sonnet | `ftl.spl` | Full-RAM L2P write/read/trim over `sim_nand` | Read-after-write + trim semantics proven by spec; **Lean Phase D** model |
| 4 WAL+checkpoint | Sonnet | `wal.spl`, `checkpoint.spl`, `superblock.spl` | WAL append/flush, A/B superblock, checkpoint begin/end+CRC | Crash-after-every-step spec; committed-prefix recovery property; **Lean Phase E** |
| 5 P2L recovery | Sonnet | `recovery.spl` | Rebuild dirty L2P from P2L + sequence IDs | Each crash-point row of research §10.2 has a passing spec; **Lean Phase F** |
| 6 DFTL map cache | Sonnet | `mapcache.spl` | Bounded map-page cache, dirty eviction, map-page checkpoint | Cache miss correctness; map-page ordering preserved across crash |
| 7 GC + wear | Sonnet | `gc.spl`, `wear.spl` | Transactional GC victim-move; dynamic+static wear leveling | GC preserves logical view; crash during GC never loses data; **Lean Phase G** |
| 8 Multicore queues | Sonnet | `shard.spl` | Per-domain ownership (namespace/LBA/band/channel) | Single-owner; no object on two cores; **Lean Phase H** |
| 9 Offload | Sonnet | `offload.spl`, `caps.spl` | Capability table + sw fallback for every hw op (CRC/XOR/bitmap/dma) | Every op has a sw reference path; hw path is payload-gated, not a no-op masquerade |
| 10 Dynamic hooks | Sonnet | `hooks.spl`, `sandbox.spl` | Signed/bounded policy hooks (GC score, QoS, hot/cold, telemetry) | Forbidden hooks (WAL/checkpoint/superblock/bad-block) are rejected at install; fuel-bounded |
| 11 Validation | Haiku ×N | `test/...crash_point_*.spl`, compliance/endurance/thermal scenario specs | One spec per crash point + NVMe compliance + power-cut/endurance matrix | Specs assert real oracles (no `expect(true)`); host-unavailable rows carry a concrete reason |
| Docs (every phase) | Haiku | `doc/06_spec/...` (generated), `doc/07_guide/...`, `*_tldr.md` | `spipe-docgen` manuals + guide updates | `0 stubs`; manual readable without source; docs-freshness gate |

## 5. Review gates (what every Opus gate checks)

A worker's output is **not done** until an Opus gate passes all of:

1. **Correctness** — module meets its frozen contract; spec assertions actually exercise the behavior.
2. **False-green audit** (repo has a documented false-green history) — no `expect(true).to_equal(true)`,
   no `pass_todo`, no empty helper, no equality-of-a-value-with-itself. Every parity/equality check
   is paired with an **absolute oracle** (known value, or proof the producer ran). Recovery specs
   assert *committed state survives*, not just "no error."
3. **Invariant check** — the phase's invariants from research §13 hold; the Lean model (if assigned)
   typechecks.
4. **Scope hygiene** — only the owned files changed; no shared-symbol rename; `bin/simple check` clean.
5. **Docs freshness** — if the phase changed workflow/contract/manual shape, the matching
   `doc/07_guide` + generated `doc/06_spec` are refreshed (SPipe completion gate, not release follow-up).

## 6. Lean4 verification track (parallel, Opus-owned)

Runs alongside implementation, not after. Each Lean phase (research §13 A–I) is one Opus work
unit producing a model + proof under `proofs/`, sequenced to land **with or just behind** the
matching implementation phase so the invariant is checked while the code is fresh:

`A pool` ‖ `B queue` (with Phase 1) → `C coroutine protocol` (Phase 2) → `D command model`
(Phase 3) → `E recovery` (Phase 4) → `F P2L/L2P` (Phase 5) → `G GC` (Phase 7) →
`H multicore` (Phase 8) → `I hang model` (cross-cutting). Proof scope stays model-level
(pools, queues, recovery protocol) — not the whole firmware binary, per research §13 caution.

## 7. Wave schedule (barriers between waves)

- **Wave 0 (serial, Opus):** Phase L interface lock — *frozen* before anything else.
- **Wave 1 (parallel):** Phase 0 (Haiku) ‖ Phase 1 pool+queue (Sonnet ×2) ‖ Lean A/B (Opus). Barrier: gates pass.
- **Wave 2 (parallel):** Phase 2 runtime ‖ Phase 3 FTL ‖ Lean C/D. Barrier.
- **Wave 3 (parallel):** Phase 4 WAL/checkpoint ‖ Phase 5 P2L recovery ‖ Lean E/F. **Hard barrier** — recovery is the heart; no later phase proceeds until committed-prefix recovery is gated green.
- **Wave 4 (parallel):** Phase 6 map cache ‖ Phase 7 GC+wear ‖ Lean G. Barrier.
- **Wave 5 (parallel):** Phase 8 multicore ‖ Phase 9 offload ‖ Lean H. Barrier.
- **Wave 6 (parallel):** Phase 10 hooks ‖ Phase 11 validation matrix (Haiku ×N) ‖ docs. Final Opus acceptance.

Within a wave, agents launch in one batch (parallel), each on a disjoint file scope; the wave's
Opus gate is the barrier. A failed gate bounces only its own work unit, not the wave.

## 8. Coordination & safety rules

- **Disjoint scopes.** Each worker owns named files; two agents never edit the same file in a wave.
- **Frozen interface.** Cross-file calls only via Phase-L signatures; renames need an Opus mini-lock.
- **Fail-fast placeholders.** Unbuilt helpers `fail(...)`/`assert(false)` — never silent stubs.
- **Compiler-bug-tail policy (critical).** The self-hosted compiler has a known bug tail
  (traits/generics/closures/option-returns/interp array-arg mutation). A worker that hits a genuine
  compiler bug must **stop working around it silently**: file a concrete bug under
  `doc/08_tracking/bug/`, pick the simplest compiling form, and flag it for the Opus gate. Never a
  silent normalization (repo rule). Prefer plain structs + free functions + int/u8 arrays; return
  values rather than relying on callee-mutated array args.
- **Run on the self-hosted binary**, not the Rust seed (SPipe default).
- **SPipe state file** `.spipe/nvme_fw_baremetal/state.md` is appended (never rewritten) by each phase:
  worker, gate verdict, bugs filed, rejected shortcuts.
- **jj commit cadence.** Commit after each gated work unit (parallel force-pushes strip ungated waves);
  ≤5-file atomic commits; work on `main`, never branch.

## 9. Acceptance (maps to `.spipe/nvme_fw_baremetal/state.md` ACs)

The lane is done when: the example builds + runs green host-side; every roadmap phase has a gated
implementation with real-oracle specs; every crash-point row recovers committed state; the assigned
Lean models typecheck; offload has a sw fallback for every op; dynamic hooks reject the forbidden set;
and the generated `doc/06_spec` manuals read as operator manuals with `0 stubs`. No phase is marked
complete on an unreviewed worker output.
