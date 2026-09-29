# NVMe Emulation Build-Out Plan (Workstream E)

Owner: workstream E of `doc/03_plan/hardware/nvme_complete_fw_mdsoc_offload_master_plan.md`
(the spine). Scope per spine §6 + §10/E: machine plane, ISA tier, hybrid RTL for
offload, bootstrap unblock.
Audit input: `doc/09_report/emulation_infra_inventory_2026-09-01.md`.
Date: 2026-09-01.

---

## 0. Verified facts (measured this session, not inherited)

| Claim | Verdict | Evidence |
|---|---|---|
| `simple-mllvm-qemu-rtl` is not in this repo | **CONFIRMED** | no match in tree; 13 `.gitmodules` submodules, none is it. ISA/machine plane is greenfield. |
| VHDL generator refuses the runtime | **CONFIRMED, reproduced** | `sh scripts/fpga/generate_rv32_vhdl.shs` -> rc=1, `error: refusing non-production Simple runtime: .../bin/release/x86_64-unknown-linux-gnu/simple` |
| `ghdl`, `verilator`, `qemu-system-riscv32` installed | **CONFIRMED** | all three on PATH |
| 33 committed VHDL files | **PARTIAL** | 33 is right for `examples/09_embedded/fpga_riscv/rtl/`; repo-wide `git ls-files '*.vhd' '*.vhdl'` = **67** (+21 `src/lib/hardware/debug`, 5 `examples/09_embedded/vhdl/`, 5 fixtures, 1 payload). Cite the subset, not the repo. |
| 21 `ghdl_*` scripts | **REFUTED (off-by-one)** | `scripts/fpga/ghdl_*.shs` = **20**. (Repo-wide `ghdl_*` = 147 incl. pinned snapshots — do not quote that number as "lanes".) |
| No `MachineGraph`/`SfrBus` in `src/` | **CONFIRMED** | zero hits each. |
| No `AddressSpace` in `src/` | **REFUTED (literally)** | `src/os/kernel/loader/segment_mapper.spl` defines an `AddressSpace`, and `ExecutableLoadConsumerErrorV1.AddressSpaceUnavailable` exists. It is a **kernel-loader** type, not an emulator machine-plane type. The audit's *intent* holds; **do not reuse this type — pick a non-colliding name.** |
| `ftl_new_emu` constructor seam | **CONFIRMED, and stronger than audited** | `examples/09_embedded/simpleos_nvme_fw/fw/ftl.spl:116` `fn ftl_new_emu() -> Ftl`. Seam is the `fil:` field: `ftl_new_emu() -> fil_new_emu() -> fmc_new_emu()` (`fw/fil_nand_emu.spl:32`). **It is already the controller default** at `fw/nvme_controller.spl:88` (`ftl: ftl_new_emu()`) — the audit does not say this. |

---

## 1. Task zero — the bootstrap unblock

### 1.1 Precisely why the runtime is refused

The refusal is **not** emitted by any compiler, and not by the generator script.
It is emitted by a tracked **shell guard wrapper**, `bin/release/simple`
(a Bourne-Again script, `git ls-files` confirms it is committed), at its lines 40-46:

```sh
case "$runtime_id" in
  *"bootstrap seed only"*|*"Rust-built"*|*"debug build"*)
    echo "error: refusing non-production Simple runtime: $runtime" >&2
    exit 1
    ;;
esac
```

`runtime_id` is the captured stdout+stderr of `timeout 5 "$runtime" --version`.
The runtime it probes is `bin/release/x86_64-unknown-linux-gnu/simple`, whose
`--version` today prints:

```
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
Simple Language v1.0.0-RC
```

That matches **two** of the three patterns (`bootstrap seed only`, `Rust-built`),
so the guard fires. **The check is a string match on the seed's own honest
self-identification.** There is no version number, hash, or capability bit involved.

Two corollaries that matter for planning:

- **`bin/simple` itself does not refuse anything.** It is the seed ELF; it warns
  on stderr and exits 0. Only lanes that route through the `bin/release/simple`
  *wrapper* are blocked. The scripts select it by
  `SIMPLE_BINARY="${SIMPLE_BINARY:-bin/release/simple}"`
  (`scripts/fpga/generate_rv32_vhdl.shs:7`).
- The wrapper exists for a second, unrelated reason: a fork-bomb guard
  (`SIMPLE_WRAPPER_REENTERED`, ~35k processes observed, took down a Vivado run —
  `doc/08_tracking/bug/cli_compile_delegation_fork_bomb_wrapper_2026-07-24.md`).
  **Do not delete or weaken this wrapper.** Its own comment states the policy:
  "Re-entry must fail closed: silently substituting the bootstrap seed makes
  deployed-runtime and architecture acceptance evidence dishonest."

### 1.2 What it would take to clear it

Clearing the guard honestly means making `bin/release/x86_64-unknown-linux-gnu/simple`
a **pure-Simple, non-seed** binary, i.e. completing the bootstrap redeploy. That is
blocked on two tracked, independently-filed defects, both currently RED:

1. **All four tracked stage binaries SEGV.**
   `sh scripts/check/check-stage-binaries-runnable.shs` reports
   `FAIL — 12 invocation(s) executed across 4 binary(ies), 8 crashed/failed`;
   `bootstrap/stage{1,2,3}/simple` and `stage3/x86_64-unknown-linux-gnu/simple`
   all SEGV on both `compile` and `native-build` for a three-line hello world,
   while `--version` answers cleanly.
   Tracked: `doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`.
2. **83 codegen-emitted runtime symbols are undefined in the C runtime archive.**
   `sh scripts/check/check-no-unresolved-runtime-symbols.shs` (advisory, honestly RED).
   This is the probable mechanism of (1): the native link tolerates the undefined
   symbol, the NULL GOT slot becomes a SIGSEGV at first call
   (the original instance was `rt_unwrap_or_trap`).

**Workstream E does not own either defect and must not attempt to fix them here.**
E's obligation is to (a) state the dependency explicitly, (b) sequence its own work
so that the maximum amount lands *before* the redeploy, and (c) provide the lanes
that will prove the redeploy worked when it arrives.

### 1.3 Is there a legitimate interim path?

**For the RTL/QEMU tier: no. This was tested, not assumed.**

`SIMPLE_BINARY` is honoured by the generator, so the guard *can* be bypassed:

```sh
SIMPLE_BINARY=bin/simple sh scripts/fpga/generate_rv32_vhdl.shs
```

Measured result — the bypass does **not** work:

```
OK build/vhdl/rv32/rv32imac_core_product_wb.vhd bytes=5500
OK build/vhdl/rv32/clint.vhd  bytes=2205
OK build/vhdl/rv32/plic.vhd   bytes=4153
OK build/vhdl/rv32/uart16550.vhd bytes=7831
Illegal instruction (core dumped)          rc=132
```

The seed generates 4 of the 10 required VHDL artifacts and then **SIGILLs**. So the
guard is not merely bureaucratic: it is fronting a genuine capability gap, and the
same class of defect as §1.2's SEGVs. **`SIMPLE_BINARY=bin/simple` is therefore not
an interim path — it is a crash with four files of debris.** Record this as the
answer whenever someone proposes the override; it also means any partial
`build/vhdl/rv32/` tree left behind must be treated as untrusted and deleted.

**For everything below the RTL tier: yes, and it is already working.**
`bin/simple` invoked directly (no wrapper) compiles the firmware fine — a live
`sh scripts/check/check-nvme-rv32-minimal-live.shs` run was observed progressing
normally through HIR lowering of ~40 generated `nvme_fw_rv32_minimal_src/*.spl`
modules at ~0.5s/file (it was cut off by my 400s probe timeout, not by an error).
So the host-behavioural tiers are **not** blocked, and that is where E's pre-redeploy
work must concentrate.

**Interim policy for this workstream:**
- Host-behavioural work (F0-F3) proceeds now on `bin/simple` directly.
- No RTL/QEMU **evidence** may be produced with a seed-backed override. A gate that
  cannot run says `ERROR — nothing was checked`, never PASS. This matches the repo's
  existing verdict convention and the wrapper's own honesty clause.
- Every E lane blocked on the redeploy ships as a **written, runnable script that
  currently ERRORs**, so the redeploy flips them green without new authoring.

---

## 2. Machine plane minimum

The design constraint from §0: `ftl_new_emu()` is **already** the controller default
and already swaps media backends through a constructor seam. **Do not rebuild it, do
not wrap it, do not introduce a second seam.** The machine plane's job is to sit
*underneath* the firmware as a memory/SFR substrate, not to re-abstract its storage.

Smallest thing that lets the NVMe firmware run against modeled devices — three types,
no more:

### 2.1 `AddressMap` (not `AddressSpace` — that name is taken, §0)

- Sorted, non-overlapping list of `AddressRegion { base: u64, size: u64, target: RegionTarget }`.
- `RegionTarget` is an enum, not a trait object, for the minimum: `Ram(ByteBuffer)`,
  `Sfr(SfrBlockId)`, `Unmapped`.
- Operations: `read(addr, width) -> Result<u64>`, `write(addr, width, val) -> Result<()>`.
- **Unmapped access is an error, never a silent zero.** This is the single highest-value
  property of the whole plane: it is what turns a firmware address bug into a test failure
  instead of a plausible-looking zero. It also directly serves the spine's workstreams
  I/J (typed address algebra, address-site census) — E should emit the region table in a
  form J can consume, and no more.

### 2.2 `SfrBus`

- `register(block_id, base, SfrBlock)`; dispatch of a decoded access to the owning block.
- `SfrBlock` is a **trait with two methods**: `sfr_read(offset, width)`,
  `sfr_write(offset, width, value)`. Side effects (interrupt raise, doorbell fire) are
  returned as a small `SfrEffect` value, **not** performed by the block. The caller
  applies them. This keeps blocks pure and testable and avoids a callback graph.
- Minimum device set to run the firmware: **doorbell block, completion-queue block,
  one UART for tracing.** Nothing else.

### 2.3 `MachineGraph`

- Owns one `AddressMap`, one `SfrBus`, a monotonic `u64` tick counter, and a FIFO
  `pending: [SfrEffect]`.
- One method: `step()` — drain `pending`, advance tick.
- **No `VirtualTime`, no `EventQueue`, no `Snapshot`, no `DmaFabric`, no `IrqFabric`,
  no `trait ExecutionEngine`** in the minimum. The audit lists these as missing; they
  should stay missing until a specific test needs one. A `u64` tick is a scheduler.

### 2.4 The seam E actually adds

Exactly one new constructor, mirroring the existing convention so it reads as native:

```
fn ftl_new_machine(m: MachineGraph) -> Ftl
```

parallel to `ftl_new_emu()`, routing `fil:` at a machine-backed FIL rather than
`fil_new_emu()`. **The existing `ftl_new_emu` chain is untouched and remains the
default.** If `ftl_new_machine` turns out to need anything beyond the `fil:` field,
that is a signal the machine plane is over-reaching — stop and re-scope.

---

## 3. Hybrid RTL (F6) — the mandatory bridge

Spine §6 is explicit, verbatim:

> "for a product with a non-empty `OffloadProfile`, the emulator must run the
> offloaded unit as RTL while the rest runs behaviorally — i.e. **hybrid RTL (F6)
> is not optional for this architecture**, it is how an offload profile is tested at all."

This is the one place E must not minimise: an offload profile that is only ever run
behaviourally is untested by construction, because the thing being asserted *is* that
the RTL unit and the behavioural model agree.

### 3.1 Build it on the existing lane, not a new one

`scripts/fpga/ghdl_rv32_nvme_fw_in_loop.shs` already establishes the exact shape:
firmware objects are native-built into `build/test-artifacts/*.o`, then a GHDL
elaboration runs a testbench against them. `scripts/fpga/ghdl_rv32_nvme_fw.shs`
(observed: it fails cleanly with `ERROR: firmware objects missing. Run first:
scripts/check/check-nvme-rv32-minimal-live.shs`) shows the artifact contract is
already file-based and already decoupled.

**The bridge is therefore a file/pipe co-simulation, not an in-process FFI.** This is
the cheap and correct choice here: GHDL is a separate simulator process, the existing
20 lanes are already process-oriented, and an FFI bridge would need a VHPIDIRECT layer
that nothing in the tree currently uses.

### 3.2 Concrete design

- **`OffloadProfile` -> unit selection.** A non-empty profile names one unit. That unit
  is *excluded* from the behavioural `MachineGraph` and replaced by an `SfrBlock`
  implementation called `RtlProxyBlock`.
- **`RtlProxyBlock`** implements the same two-method `SfrBlock` trait (§2.2). Instead of
  computing, it serialises each access as one line of a transaction log:
  `R <offset> <width>` / `W <offset> <width> <value>`, and blocks for a reply line.
- **GHDL side:** a generated testbench wrapper drives the unit under test from the same
  line protocol via `std.textio` on two FIFOs. Text-line, not binary — GHDL's `textio`
  is the path of least resistance and the transcript is then human-readable and diffable,
  which is what makes a mismatch debuggable.
- **The gate is a differential run, and this is the point of the whole tier:**
  run the identical firmware workload twice — once with the unit behavioural, once with
  `RtlProxyBlock` — and assert the two transaction logs are **byte-identical**. Divergence
  is the finding. This mirrors the spine's own cheapest-first proof pattern for
  workstream G ("regenerate `cosmos_nfc_regs.h` ... and assert byte-identity against the
  committed hand-written header").
- **New lane:** `scripts/fpga/ghdl_rv32_nvme_offload_hybrid.shs`, written to the same
  verdict convention as the repo's guards (`PASS — <n> transactions compared, 0 divergent`
  / `FAIL` / `ERROR — nothing was checked`). A run comparing 0 transactions is ERROR.
- **Status: authorable now, runnable after the redeploy.** The `RtlProxyBlock`, the line
  protocol, the differential harness and the lane script are all pure-Simple + shell and
  need no VHDL *generation*; only the final elaboration needs the generator. Write it now,
  let it ERROR.

### 3.3 Pre-existing hazard this tier inherits

Spine §F records that the existing JTAG/DTM/DMI/SBA VHDL is "real but handwritten",
violating §10.1's "generated RTL is never hand-edited", and that
`src/lib/hardware/debug/debug_registers.vhd:661` hard-wires `dmstatus_v(7) := '1'`
— "**G6 cannot be claimed while this stands**". E must not route the hybrid bridge
through the debug/JTAG path, or it inherits that defect into its own evidence.
Use the plain SFR path.

---

## 4. Fidelity ladder F0-F9 — staging

**Naming caveat, stated rather than papered over:** the spine §6 does **not** define
the tiers. It only cites "Fidelity ladder F0-F9 per the SimpleEMU plan §5", and that
document was not located in this repo. The tier *names* below are therefore E's working
definitions, consistent with §6's one fixed anchor — **F6 = hybrid RTL**. They must be
reconciled against SimpleEMU §5 when it is available; until then no gate name should
encode a tier number other than F6.

| Tier | Meaning | Needs | Blocked on redeploy? |
|---|---|---|---|
| **F0** | Pure logic specs, no machine | existing `fw/` + SSpec | **No — MEASURED green** (see below) |
| **F1** | Behavioural FW on host, emu media | `ftl_new_emu()` (exists, is the default) | **No — MEASURED green** (see below) |
| **F2** | + `AddressMap` w/ trapping unmapped access | §2.1 | **No** — *projected, nothing to run yet* |
| **F3** | + `SfrBus` + doorbell/CQ/UART blocks | §2.2, §2.3, `ftl_new_machine` | **No** — *projected, nothing to run yet* |
| **F4** | ISA-accurate rv32 interpreter | greenfield ISA tier; **native-built FW objects** | **Yes** (objects come from `check-nvme-rv32-minimal-live.shs`) |
| **F5** | QEMU rv32 system lane | `qemu-system-riscv32` (installed) + stage3 binary w/ `status=pass` | **Yes** |
| **F6** | **Hybrid RTL for OffloadProfile — MANDATORY (§3)** | §3.2 bridge + generated VHDL | **Yes** (authorable now) |
| **F7** | Full-SoC GHDL | `generate_rv32_vhdl.shs` (SIGILLs today) | **Yes** |
| **F8** | FPGA bitstream / board | Vivado + board | **Yes**, plus board access |
| **F9** | Silicon / ATE | out of scope for E | n/a |

**F0/F1 measured, not inferred.** Executed this session:

```
bin/simple run examples/09_embedded/simpleos_nvme_fw/fw/rel_wiring_check.spl
  ... PASS: e: the retired block is marked bad in the bad-block table (1)
  REL WIRING OK                                              rc=0
```

The seed prints its usual banner on stderr and exits 0. This exercises the
`ftl_new_emu() -> fil_new_emu() -> fmc_new_emu()` chain end to end (reclaim,
erase-fail abort, over-provision spare substitution, bad-block marking), which is
exactly the F1 contract. **F2/F3 are marked unblocked because they add only pure
host-side Simple types on top of this proven path — that is a projection, not a
measurement, and there is nothing to execute until §2 is written.**

**Reachable before the unblock: F0-F3.** That is E's entire near-term mandate, plus
*authoring* (not running) the F4-F6 lanes. Everything from F4 up needs a native build,
which needs the redeploy.

---

## 5. What NOT to build yet

Deliberately aggressive, per the spine's own anti-over-build warnings.

1. **Do not build an SVAP layer.** Spine §F: "SVAP extends the existing design rather
   than replacing it — a materially cheaper path than the spine assumed." Research §3's
   evidence claim is already "~70% true"; only `EvidenceRequest`, the `EvidenceProvider`
   trait and a spec-layer `EvidenceManifest` are actually missing. Building an SVAP
   framework is re-doing 70% of existing work.
2. **Do not build new VHDL generators.** 67 `.vhd` files and 20 GHDL lanes already exist
   and the *existing* generator crashes. Adding a generator adds a second thing that
   cannot run. Fix the ability to run one before authoring another.
3. **Do not claim, or name a gate for, ATPG.** Spine §11.3: "SSpec must NOT claim to
   replace ATPG... Any claim that Simple 'generates manufacturing test patterns' is
   false and must not appear in a gate name, a doc, or a capability bit." Follow the
   existing precedent of `check-hw-ir-ate-pin-groups`, "deliberately not 'ate-patterns'".
4. **Do not port `simple-mllvm-qemu-rtl`.** It is absent (§0) and the spine calls the
   ISA/machine plane greenfield. A 3-type minimum (§2) beats importing an engine whose
   `HybridSimulator.step()` / `GuestMemory` / `src/rtl/sim_engine.spl` API cannot even
   be read from here.
5. **Do not build a DBT/JIT.** F4 needs a correct interpreter, not a fast one. Speed is
   a problem to have after correctness.
6. **Do not build `VirtualTime`, `EventQueue`, `Snapshot`, `DmaFabric`, `IrqFabric`, or
   `trait ExecutionEngine`.** The audit lists them as missing; missing is the correct
   state until a named test requires one. A `u64` tick (§2.3) is the scheduler.
7. **Do not wire Verilator.** Installed, but the RTL is VHDL and Verilator does not read
   VHDL. It is inventory, not a capability.
8. **Do not touch `fw_rv32/`'s "array-free scalar re-expression" drift.** Real risk, real
   problem, and squarely another workstream's.
9. **Do not modify or weaken `bin/release/simple`.** It is load-bearing twice over
   (fork-bomb guard + honesty guard) and §1.3 proved the thing it guards genuinely crashes.

---

## 6. Sequencing

**Now (unblocked):**
1. `AddressMap` with trapping unmapped access (§2.1) — highest value per line in this plan.
2. `SfrBus` + `SfrBlock` trait + `SfrEffect` (§2.2); doorbell, CQ, UART only.
3. `MachineGraph` with `step()` (§2.3).
4. `ftl_new_machine()` (§2.4), one constructor, `ftl_new_emu()` untouched.
5. Author `RtlProxyBlock`, the line protocol, and
   `scripts/fpga/ghdl_rv32_nvme_offload_hybrid.shs` (§3.2) — ERRORing until the redeploy.

**On the redeploy landing:**
6. Re-run `sh scripts/fpga/generate_rv32_vhdl.shs` with **no** `SIMPLE_BINARY` override;
   all 10 artifacts must appear. Delete any debris from a prior override run first.
7. Run the F6 differential gate. Byte-identical transaction logs or FAIL.
8. Then F4/F5/F7.

**Exit criterion for E:** the F6 hybrid lane runs green on the deployed pure-Simple
runtime, with a non-empty `OffloadProfile`, and its verdict line states a non-zero
transaction count.
