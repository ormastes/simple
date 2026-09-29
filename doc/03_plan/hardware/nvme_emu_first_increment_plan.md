# NVMe Firmware + Emulator: Minimum Viable First Increment

**Date:** 2026-09-01
**Status:** Proposed first increment — narrows two larger plans
**Scope:** 4-6 weeks, single developer

Narrows `nvme_ssd_firmware_hardening_design_plan.md` (Slices A-E) and
`simpleemu_unified_emulator_nvme_riscv_test_infra_plan.md` (Waves 0-12) to the
first increment that produces hardened firmware plus enough emulation infra to
test it through.

Supporting audits, both dated 2026-09-01:

- `doc/09_report/nvme_fw_current_state_audit_2026-09-01.md`
- `doc/09_report/emulation_infra_inventory_2026-09-01.md`

---

## 0. Premise correction (blocking, read first)

`examples/09_embedded/simpleos_nvme_fw/fw/fil_nand_emu.spl:28` states:

> "`fil.spl` currently hardcodes `NandDevice` with no backend-selection seam
> (adding that seam is out of scope here)."

This is **stale on both of its claims**. The seam exists:

- `fw/ftl.spl:116` — `fn ftl_new_emu() -> Ftl`
- `fw/fil.spl:98` — `fn fil_new_emu() -> Fil`
- `fw/fil_fmc.spl:75` — `fn fmc_new_emu() -> Fmc`

And the same docstring's companion claim — that "end-to-end fil/ftl has NOT
been exercised on it" — is refuted in-tree by
`fw/fil_nand_emu_e2e_check.spl:50,95,115`, which builds `ftl_new_emu()` and
runs it end to end. Five further callers exist (`rel_ladder_check.spl:161`,
`rel_wiring_check.spl:57`, `rel_seams_check.spl:86`, and the e2e check).

The constructor-level backend seam is therefore *already* the "MachineGraph
shim" both large plans propose to build. Task 1 corrects the docstring; every
later task depends on this being understood, or effort is wasted rebuilding an
existing seam.

## 0.5 Reconciliation with the infra inventory

The inventory audit changes two assumptions this plan would otherwise inherit
from the SimpleEMU document.

**`simple-mllvm-qemu-rtl` is absent from this repo.** Not a submodule, not
vendored, not on disk. Four of SimpleEMU §3.2's ten truth-reset rows (fast RV32
mode, ELF loading, MMIO, native RTL engine) describe code that is not here. The
ISA-execution family and machine plane are greenfield, not a repair job. This
*reinforces* the choice below: an increment that depends on that engine cannot
start at all.

**Every VHDL generator and QEMU lane is gated on a production Simple runtime.**
Generators fail with `refusing non-production Simple runtime:
bin/release/x86_64-unknown-linux-gnu/simple`; QEMU lanes require a stage3 binary
with `status=pass` provenance. This is the same bootstrap-redeploy blockage
already tracked for the stage binaries. Consequences for task ordering:

- Tasks 1, 4, 5, 6, 7 are **host-native** (`bin/simple run` / `bin/simple test`)
  and are unaffected. They are the increment's core and can proceed today.
- Tasks 2 and 3 edit GHDL/QEMU inputs. Task 2 (Simple-side slot map + drift
  check) is host-runnable. **Task 3's verification step cannot pass until the
  bootstrap blockage clears** — write it, but expect to land it behind the
  redeploy, and do not report it green on an unverified lane.
- Task 8 is doubly blocked and stays optional.

Do not treat the bootstrap redeploy as adjacent work. It is the critical path
for the entire RTL/QEMU tier, and this increment is deliberately structured so
that most of it does not wait on that.

---

## 1. Which vertical slice is first

**Chosen: hardening-plan Slice B — "One-page write/read through T1 model" —
executed host-native on the existing `fw/` stack with the `fil_nand_emu`
backend, with hardening Slice C reduced to its typed-slot-map component and
landed independently.**

| Candidate | Verdict | Reason |
|---|---|---|
| Hardening Slice A (read-only Identify) | **No** | Its gates ("no raw MMIO outside controller service", "profile-generated BAR/queue constants", "no heap") all require the profile/RegisterIR generator to exist first. Identify is also the lowest-risk NVMe path — no FTL, no media, no ECC, no recovery, i.e. none of the code likely to harbour real bugs. Low value per unit of generator work. |
| **Hardening Slice B (one-page write/read)** | **Yes** | Exercises the full `HIL -> FTL -> FIL -> NAND` chain the firmware exists to implement. Its gates ("full page/OOB model, not scalar"; "test faults through `MediaTestControl` only") are both reachable now: `fil_nand_emu` gives real page+OOB+Vt physics, and the typed test-control port is Task 3. The only slice whose gates are satisfiable without a code generator. |
| Hardening Slice C (RV32 RTL migration) | **Partial** | The `.nandram` replacement is the highest-value hardening fix in the repo and lands standalone. The full slice also demands differential old-vs-new trace comparison across GHDL, needing a trace normalizer that does not exist — and a GHDL tier that currently cannot run. Take the slot map; defer the differential. |
| Hardening Slices D/E (Cosmos+, multi-queue) | **No** | Require hardware and a correctness baseline that does not yet exist. |
| SimpleEMU Slice A (register->behavioral->RTL) | **No** | Five new generators plus a new artifact format (SVAP) before one firmware defect is found. The existing constructor seam already delivers the backend-swap capability this slice builds toward, at zero generator cost. |
| SimpleEMU Slice B (same-source one-command NVMe) | **Deferred — but it is the second increment** | Correct destination. Blocked on a normalized-observation format. Land Slice B host-native first; add the RV32 leg once the host leg is green and the observation shape is known empirically rather than designed up front. |

Value delivered: the FTL/FIL/ECC/recovery paths get exercised end to end
against media that actually decays, the raw `.nandram` coupling goes away, and
every step has a runnable check.

## 2. Smallest shim to run `fw/` against a behavioral model

**There is no shim to build.** The requirement is already met by
`ftl_new_emu()`. What is missing is selection plumbing and coverage.

1. **A backend selector value, not a type system.** One enum
   (`MediaBackend.Behavioral | MediaBackend.VtPhysics`) plus
   `ftl_new_with(backend)` dispatching to the two existing constructors.
   `ftl_new()` keeps its current behaviour. ~30 lines in `fw/ftl.spl`.
2. **Thread it to the controller.** `fw/nvme_controller.spl` and
   `fw/nvme_main.spl` construct the FTL; give them the same optional
   parameter, defaulting to `Behavioral`. Production composition unchanged,
   default path untouched — that is the isolation argument for increment one.
3. **Close the two known divergences.** `fil_nand_emu`'s docstring documents
   them honestly: erased pages read `FFh` (not `0`), and `err` carries a
   physics-derived bit-error count (not just injected). Any FTL/ECC assertion
   assuming `0`-on-erased will fail under the physics backend. **This is the
   increment's bug-finding surface** — those failures are the deliverable, not
   an obstacle. Each is either a genuine firmware defect or a test that
   encoded the placeholder backend's behaviour.
4. **Accept the geometry fold.** Firmware addresses 64 blocks x 64 pages; the
   S1 NeChip backs 8 x 4, and `emu_fold_row` aliases beyond that. For Slice B
   stay inside `block < 8, page < 4` where the map is 1:1 and round-trips
   exactly. Do not widen emulator geometry in this increment.

**Explicitly not built:** `MachineGraph`, `AddressSpace`, `SfrBus`,
`DmaFabric`, `IrqFabric`, RegisterIR, `@reg` surface, register-block IDs. The
SimpleEMU plan motivates these by the need to swap device implementations
behind firmware; the constructor seam already does that for the one device that
matters. Revisit when a *second* peripheral needs the same treatment — that is
the honest trigger condition, not a wave number.

There is a second, independent behavioral stack in `simpleos_nvme_fw/emu/`
(`nvme_emu_main.spl`, `nand_onfi.spl`, `ftl_emu.spl`, Lean4 proofs, green under
`bin/simple run`). It is a *host/device pair with its own FTL*, not a media
backend for `fw/`. Use it as the **independent oracle** for Task 7. Do not
merge the two stacks in this increment.

## 3. Replacing raw `.nandram` — standalone landable change

### The actual defect

**Scope correction (measured 2026-09-01).** This section originally estimated
~16 slots, taken from the subset the testbench pokes. The firmware actually
uses **49 distinct indices (0-48)**, plus 64 as a deliberate out-of-region
probe, across ~250 call sites — and no layout documentation existed anywhere in
the tree. Task 2's 2-3d sizing below is therefore low. See
`doc/08_tracking/bug/nandram_slot_map_undocumented_and_two_vacuous_slots_2026-09-01.md`,
which also records two defects the naming exposed (slots 23/24 redundant; slot
31 a vacuous always-passing evidence digit).

The `.nandram` region is 64 words / 256 bytes. Individual word indices carry
distinct semantics and are hardcoded as bare integers in **three** places with
no shared definition:

- `fw_rv32/entry.spl` — `_nand_ram_load(14)`, `_nand_ram_store(48, 1)`,
  `_nand_ram_load(9)`, `_nand_ram_load(47)`, `_nand_ram_store(47, ...)`,
  `_nand_ram_load(35/36/7/8/23/24/20/46)` in the evidence emitter.
- `examples/09_embedded/fpga_riscv/rtl/tb_rv32_nvme_fw_in_loop.vhd` —
  `ram(G_NANDRAM_WORD + 4)` (read level), `+ 25` (force verify failure),
  `+ 7` (refreshes), `+ 8` (recoveries), `+ 21` (reads), `+ 24` (remaps),
  `+ 44` (alternate), plus `assert G_NANDRAM_WORD + 47 < RAM_WORDS`.
- `scripts/qemu/qemu_rv32_nvme_fw_in_loop.shs` — GDB
  `set {unsigned int}<addr>` / `x/wx` at computed offsets from
  `_nandram_start`.

Plus brittle coupling in `scripts/fpga/ghdl_rv32_nvme_fw_in_loop.shs`: it
`nm`-extracts `_nandram_start`/`_nandram_end` and **hard-fails unless the
region is exactly 256 bytes** (line 32). Adding one counter breaks GHDL.

Nothing detects drift between the three copies. Renumber a slot in `entry.spl`
and the testbench silently injects a fault into the wrong field, or reads a
counter that has moved — a test that passes while measuring nothing.

### The minimal fix (transport unchanged)

Single source of truth for slot names/indices; keep the RAM-poke transport.

1. **`fw_rv32/nand_test_slots.spl`** — one named constant per live slot, each
   with a one-line semantic comment and a role tag (`inject` vs `observe`):
   `NAND_SLOT_READ_LEVEL = 4`, `NAND_SLOT_REFRESHES = 7`,
   `NAND_SLOT_RECOVERIES = 8`, `NAND_SLOT_READS = 21`,
   `NAND_SLOT_REMAPS = 24`, `NAND_SLOT_FORCE_VERIFY_FAIL = 25`,
   `NAND_SLOT_ALTERNATE = 44`, `NAND_SLOT_SERVICE_COOKIE = 47`,
   `NAND_SLOT_ADMINQ_READY = 48`, etc. Include `NAND_SLOT_COUNT` and
   `nand_slot_name(i) -> text`.
2. **`entry.spl` uses the names**, never integers. Mechanical substitution.
3. **Emit the map once at build time.** `fw_rv32/build.shs` already generates C
   and asm; have it also emit `build/nand_slots.env`
   (`NAND_SLOT_READ_LEVEL=4` ...) and `build/nand_slots_pkg.vhd` (a VHDL
   constant package). Shell scripts source the `.env`; the testbench uses the
   package instead of `G_NANDRAM_WORD + <literal>`.
4. **Drift check** — `fw_rv32/nand_slot_drift_check.spl`, modeled directly on
   the existing `fw_rv32/const_drift_check.spl` and `ipc_drift_check.spl`
   (same pattern, same runner). Asserts: every constant unique; all
   `< NAND_SLOT_COUNT`; `entry.spl` contains no bare `_nand_ram_load(<int>)` /
   `_nand_ram_store(<int>` call; generated `.env`/`.vhd` agree with the Simple
   constants.
5. **Delete the 256-byte assertion.** `ghdl_rv32_nvme_fw_in_loop.shs:32`
   becomes `>= NAND_SLOT_COUNT*4`, sourced from the generated env.

**Why not the full `MediaTestControl<M>` trait now.** Hardening plan §12.7
specifies a trait with a production-linker-exclusion guarantee ("the production
linker graph has no `MediaTestControl` implementation"). That needs
linker-graph analysis and an AOP access manifest (§13.6) that do not exist —
and the firmware audit confirms AOP still parses only
execution/call/within/attr/effect-string predicates, with get/set/effect
deferred. The slot map kills the actual bug — undetected three-way drift — at
roughly a tenth of the cost, and is a strict prerequisite for the trait anyway:
the trait's method set is exactly the slot map's `inject`/`observe` partition.
Land the map, harvest the method set from it, promote later.

**Landable standalone:** touches no FTL/FIL logic and no firmware behaviour.
All existing markers in `scripts/check/check-rv32-nvme-nand-recovery.shs` must
still pass byte-identically — that is the regression proof. See §0.5 on when
that verification can actually run.

## 4. Task ordering and sizing

Each task has one runnable check and lands independently. Pattern every new
shell check on `scripts/check/check-rv32-nvme-nand-recovery.shs`:
`STATUS: FAIL <name>: <reason>`, ordered unique markers, plus a `self_test()`
proving the checker rejects a truncated/misordered log.

| # | Task | Size | Gated? | Runnable check |
|---|---|---|---|---|
| 1 | Correct the stale `fil_nand_emu.spl:28` docstring (both claims); document the `ftl_new_emu` seam in `fw/CONVENTIONS.md`. | 0.5d | no | `bin/simple check` on `fw/`; grep assertion in the Task-7 spec that the "no backend-selection seam" sentence is gone. |
| 2 | `nand_test_slots.spl` + `entry.spl` substitution + `nand_slot_drift_check.spl`. No generation yet. | 2-3d | no | `bin/simple run .../fw_rv32/nand_slot_drift_check.spl`. |
| 3 | Emit `nand_slots.env` + `nand_slots_pkg.vhd` from `build.shs`; convert the VHDL testbench and the QEMU/GHDL scripts to named slots; drop the 256-byte assert. | 3-4d | **yes** | GHDL + QEMU lanes produce the identical marker sequence as before. Prove by adding a 65th slot and confirming both still pass. **Blocked on bootstrap redeploy.** |
| 4 | `MediaBackend` enum + `ftl_new_with` + controller/`nvme_main` plumbing, default `Behavioral`. | 1-2d | no | New `fw/media_backend_check.spl`: `ftl_new()` and `ftl_new_with(Behavioral)` observationally identical; `ftl_new_with(VtPhysics)` reaches `NeChip`. |
| 5 | **Slice B host-native**: one page write then read through `HIL -> FTL -> FIL -> NandEmu`, inside the 1:1 geometry window. Expect erased-page-`FFh` and bit-error-count failures; triage each as firmware defect vs. test-encoded-placeholder and fix. | 4-6d | no | `fw/slice_b_page_rw_check.spl` — program, read, verify data + OOB {lba,seq} + ECC + `err == 0` clean. |
| 6 | Fault injection through the typed path only: `set_block_wear` / `advance_time_s` / `set_vref_offset` to age a block; prove a correctable single-bit error then an uncorrectable one, and that the FTL observes and recovers. | 3-4d | no | `fw/slice_b_recovery_check.spl` + a negative test asserting no test hook reaches the model except via the named seam. |
| 7 | SSpec wrapper `test/03_system/app/nvme_firmware/nvme_slice_b_media_spec.spl`, following `rv32_nvme_nand_read_level_spec.spl`. Cross-check the FTL's L2P outcome against the independent `emu/ftl_emu.spl` oracle. | 2-3d | no | `bin/simple test` on the new spec. |
| 8 | *(Optional)* Recompile the Task-5 modules for RV32 and compare the marker sequence to the host run — the cheap half of SimpleEMU Slice B, no normalizer. | 3-5d | **yes** | Existing QEMU firmware-in-loop script extended with Slice B markers. |

Tasks 2 and 3 are independent of 1 and 4-7 and can proceed in parallel.
Total ~4-6 weeks. Tasks 1, 2, 4-7 need no bootstrap redeploy.

Per repo rule, every fix here ships with a spec that fails before the fix and
passes after, plus defect-class neighbours.

## 5. Explicitly deferred

Reuse the existing SSpec runner, `scripts/check/*.shs` conventions, and the
`const_drift_check.spl` / `ipc_drift_check.spl` drift pattern. Build no new
test framework in this increment.

| Deferred | From | Why |
|---|---|---|
| RegisterIR / PinIR / ProtocolIR / EffectIR generators | SimpleEMU W1, §7.1 | The constructor seam already provides device substitution for the one device that matters. Trigger to revisit: a second peripheral needs the same swap. |
| `MachineGraph` / `AddressSpace` / `SfrBus` / `DmaFabric` / `IrqFabric` | SimpleEMU W3, §4.3-4.4 | Same. Motivated by a decoupling problem `ftl_new_emu` has already solved here. |
| SVAP v1 and the SVAP pack format | SimpleEMU W1, hardening §15 | A new artifact format with no consumer. SSpec + shell markers already carry evidence and are wired into CI. |
| Full `MediaTestControl<M>` trait + production-linker exclusion proof | Hardening §12.7 | Needs linker-graph analysis + AOP access manifest; AOP's get/set/effect pointcuts are still deferred. Slot map kills the real bug now and yields the trait's method set for free. |
| Fidelity ladder F2+ (timed behavioral, deterministic parallel, schedule exploration, snapshot/replay) | SimpleEMU §5-6 | F1 has not found its first bug yet. Concurrency/timing fidelity is worthless before functional correctness. |
| AOP raw-access rejection pointcuts | Hardening §13 | The slot-map drift check covers the one real leak path at a fraction of the cost. |
| Profile system / controller-media certification records | Hardening §8 | One controller, one media model. A profile system with one profile is configuration theatre. |
| Mutation testing, fuzzing, host differential suite | Hardening §14.6, §15.4, §15.8 | Require a passing baseline that does not exist. |
| Slices D (Cosmos+) and E (multi-queue) | Hardening §22 | Need hardware and a correctness baseline. |
| SimpleEMU Waves 4-12; the absent `simple-mllvm-qemu-rtl` engine | SimpleEMU §15 | Downstream of everything above, and the engine is not in this repo at all. |
| Lane consolidation (`fw/` vs `fw_rv32/` vs `fw_rv64/`) | Hardening M2/M4 | Real and worsening — three lanes now, sharing only `README.md` — but consolidating is a larger change than one increment. Do not add features to `fw_rv32`/`fw_rv64` meanwhile. |
| Widening emulator geometry past S1 (8 blocks x 4 pages) | — | Stay in the 1:1 window; aliasing is documented and acceptable for one increment. |

## 6. Exit criteria

1. `fil_nand_emu.spl`'s stale claims (no seam; not exercised end to end) are
   corrected.
2. No bare NAND slot integer appears in `entry.spl`, the VHDL testbench, or the
   shell scripts; the drift check fails if one is reintroduced.
3. The `.nandram` region can grow past 256 bytes without breaking GHDL.
4. A page write/read/recovery round trip runs through `ftl_new_emu` with real
   Vt drift, and every divergence found is triaged and closed.
5. All pre-existing markers in `check-rv32-nvme-nand-recovery.shs` still pass.

Criteria 2, 3 and 5 depend on the bootstrap redeploy (§0.5); 1 and 4 do not.

---

## 7. Execution log (2026-09-01)

| Task | State | Evidence |
|---|---|---|
| 1 — correct stale `fil_nand_emu.spl` docstring | **DONE** | both false claims removed; `fil_nand_emu_e2e_check` rerun RC=0 to back the replacement text |
| 2 — slot map + drift check | **DONE (map half)** | `nand_test_slots.spl` (49 slots), `nand_slot_drift_check.spl` — `checked 49 slots in a 64-word region, 0 drift`; proven red by 2 mutations, each with a control |
| 3 — generate `.env`/VHDL pkg, convert testbench + scripts | **BLOCKED** | needs the GHDL/QEMU lanes for its byte-identical-marker regression proof; see §0.5 |
| 4 — controller-level emu backend seam | **DONE** | `nvme_controller_new_emu()` / `nvme_controller_new_emu_for_target()`; default constructors untouched |
| 5 — Slice B host-native | **DONE** | `fw/nvme_emu_media_check.spl` — 16 PASS, `NVME EMU MEDIA OK`; proven red by 2 mutations (ageing removed; behavioural backend substituted) |
| 6 — fault injection via typed path only | **DONE (folded into 5)** | sections C/D use `emu_set_block_wear` / `emu_advance_time_s` exclusively; zero raw media or `.nandram` access, asserted by the spec with a positive control |
| 7 — SSpec wrapper | **DONE** | `test/03_system/app/nvme_firmware/nvme_emu_media_slice_b_spec.spl` — `2 examples, 0 failures`, explicit verdict line |
| 8 — RV32 leg | **BLOCKED** | same gate as task 3 |

Six of eight tasks landed. The two blocked ones are blocked on the bootstrap
redeploy, not on design.

### Oracle correction made during task 5

The first draft of the Slice B check used `emu_read_margin` as its non-vacuity
oracle. The margin did not move under 3000 P/E + 1 year (60 -> 60), and two
hypotheses were eliminated before concluding the oracle was wrong rather than
the firmware: lazy drift materialisation (re-sampled after the sense — still
60) and DRAM-write-buffer masking (read path confirmed to reach
`ftl.read_range_status`). The check now uses the witness
`fil_nand_emu_e2e_check.spl` already establishes as load-bearing — a raw
offset-0 device read sensing `0xFF` and failing ECC.

Recorded because the failed oracle is worth knowing about: `emu_read_margin`
did not respond to wear+retention on this path, and whether that is expected
(margin is nominal-lobe geometry, not drift state) or a gap in the Vt model has
not been determined. It is not a blocker for Slice B, which now has a working
witness, but anyone reaching for margin as a drift oracle should measure it
first.
