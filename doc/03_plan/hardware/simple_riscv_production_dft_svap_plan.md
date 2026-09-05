# Simple RISC-V Production, Debug/DFT, and the Simple Verification Artifact Pack (SVAP)

**Workstream F** of `nvme_complete_fw_mdsoc_offload_master_plan.md` (read §11, especially §11.3).
**Date:** 2026-09-01
**Goal owned:** G6 — *Simple RISC-V must support manufacturing verification through SSpec
(ATE / hardware test-house functional test), AND the same SSpec scenario must still run as an
ordinary `bin/simple test` run.* One scenario, two projections — never two maintained suites.

**Source requirements implemented here:**
`simpleemu_unified_emulator_nvme_riscv_test_infra_plan.md` §2.1-2.4 (invariants),
§7.4 (PinIR/PadIR), §10.1-10.10 (RISC-V production/debug/DFT/release gates),
§11.1-11.11 (SVAP).

**Reading convention, enforced throughout.** Every claim is tagged:

- **MEASURED** — verified in this repository at the cited `file:line` on 2026-09-01.
- **INFERRED** — a reasonable deduction from measured facts; not itself verified.
- **PROPOSED** — does not exist; this plan is asking for it to be built.

An untagged sentence in §2 is measured; an untagged sentence in §3 onward is proposed.

---

## 1. The honesty boundary, stated before anything else

This is stated first, at full strength, because it is the single claim most likely to be
oversold and the one the master plan (§11.3) and EMU invariant 8 both single out.

> **SSpec projects FUNCTIONAL vectors to ATE. It does NOT replace ATPG.**
>
> Scan stuck-at and transition-delay patterns are produced by an **external ATPG tool run on
> a scan-inserted netlist**. SSpec/SVAP may **configure, package, schedule, execute, compare,
> and trace** those patterns, and may bind them into the evidence manifest. SVAP cannot
> independently derive high-quality structural fault coverage from functional intent, and it
> does not compute fault coverage numbers of its own.
>
> **Any wording implying Simple "generates manufacturing test patterns" is false.** It must not
> appear in a gate name, a capability bit, a doc heading, a commit message, or a release claim.

Two mechanical consequences, both binding on the deliverables below:

1. **Banned-phrase gate.** `check-svap-atpg-claim-hygiene.shs` (§6.7) scans gate names, SVAP
   capability bits, and this workstream's docs for the forbidden claim forms
   (`generat* (manufactur|scan|ATPG|fault) *pattern`, `fault coverage` asserted by SVAP,
   `replaces ATPG`). It is fail-closed and non-vacuous.
2. **Typed provenance, not prose.** Every SVAP pattern artifact carries
   `origin: SvapAuthored | ExternalAtpg | ExternalLab`. `ExternalAtpg` artifacts are
   **import-only**: no SVAP code path may synthesize one, and the coverage record for them
   carries `coverage_authority: external_tool` with the tool name and version. A pattern with
   `origin: SvapAuthored` claiming stuck-at coverage is a hard schema error.

What SSpec *does* legitimately own, per §10.9: **intent, campaign orchestration, scheduling,
comparison, evidence, and results** across all test categories — including the ATPG category.
That is a real and valuable role. It is not pattern generation.

---

## 2. Measured current state

### 2.1 What SSpec is today

**MEASURED.** `bin/simple test` is a wired CLI subcommand (`src/app/cli/dispatch/table.spl:103`,
`name: "test"`), backed by the applications under `src/app/test/`, `src/app/test_runner_new/`,
`src/app/test_daemon/`, plus `src/app/composite_test_entry.spl`. Specs are ordinary `.spl`
files using `describe`/`it`/`step`/`expect`; the spec library lives under
`src/lib/common/spec/` and `src/lib/nogc_sync_mut/spec/`. **MEASURED:** `find test -name
'*_spec.spl'` returns **21,510** spec files (raw count; the repo maintains known duplicate
mirror test trees — `test/01_unit/` vs `test/unit/`, `test/02_integration/` vs
`test/integration/`, fenced by `scripts/check/check-test-tree-divergence.shs` — so the count of
*distinct* specs is lower; the order of magnitude is what matters here). Any SVAP design that
requires editing those files to keep working is dead on arrival — see §3.6.

**MEASURED**, a second, separate layer exists: spec *maintenance* tooling, distinct from the
runner. `src/app/sspec_maintain/` holds `analyzer.spl`, `rules.spl`, `score.spl`,
`scaffold.spl`, `documentize.spl`, `improve.spl`, `report.spl`, `lifecycle.spl`, `cache.spl`,
`source_facts.spl`, `suppression.spl`, `model.spl`, `main.spl`; `src/app/spec_to_sspec/` holds
the conversion path including `spipe_evidence_emit.spl`. **INFERRED:** these scaffold, score,
and documentize specs — they do not execute them — so SVAP's authoring surface (§3.6) will need
a corresponding `sspec_maintain` rule so a scaffolded spec can opt into an intent, but they are
not on the execution path and F does not modify them.

**MEASURED, negative:** `src/compiler/90.tools/` contains `lint/`, `duplicate_check/`,
`coverage.spl`, `api_surface.spl`, `depgraph/`, `formatter/`, `fix/`, `sffi_gen/`, `perf/`,
`stats/`, `semantic_diff.spl`, `aop.spl` and siblings — **no spec-runner or evidence content**.
The compiler tools layer is not part of the SSpec execution path and F does not touch it.

### 2.2 The research §3 "modern SSpec evidence design" claim — verified noun by noun

The research asserts a design that "already defines typed evidence requests, providers,
adapters, comparators, selectors, manifests, and Markdown projection." Checked individually:

| Noun claimed | Verdict | Evidence |
|---|---|---|
| Evidence **selectors** | **EXISTS as code** | `src/lib/common/spec/evidence/model.spl:29` `pub enum EvidenceSelectorKind`, `:48` `pub struct EvidenceSelector`, constructors `:56-151` (node / field / json-pointer / terminal-region / pixel-region / binary-field / byte-range) |
| **Oracles** (typed checks) | **EXISTS as code** | `model.spl:175` `pub enum OracleMode`, `:211` `pub struct OracleCheck`, `:223` `pub struct OracleSpec`, constructors `:240-316` (exact, full-pattern, ignore, multiset, ordered, numeric-tolerance, bind, same-as) |
| Canonical evidence + status | **EXISTS as code** | `model.spl:326` `EvidenceNode`, `:333` `CanonicalEvidence`, `:382` `EvidenceStatus`, `:397` `EvidenceCheckResult` |
| Format **adapters** | **EXISTS as code**, though not named `EvidenceAdapter` | `src/lib/common/spec/evidence/format/` — `binary_layout.spl`, `layout_schema.spl`, `exec_capture.spl`, `file_capture.spl`, `terminal_grid.spl`, `text_protocol.spl`, `json_document.spl`, `simulation_profile.spl`, `audio_profile.spl`, `ml_profile.spl`, `scene_profile.spl`, `evidence_sidecar.spl` |
| **Comparator** | **EXISTS as code** | `src/lib/common/spec/evidence/evidence_comparator.spl` |
| **Providers** | **EXISTS as code** (counterpart providers) | `src/lib/nogc_sync_mut/spec/evidence/counterpart/` — `provider_registry.spl`, `provider_runner.spl`, `native_provider.spl`, `process_provider.spl`, `dynlib_provider.spl`, `worker_provider.spl`, `chrome_dom_snapshot_provider.spl`, `cipher_sha256_provider.spl`, `host_vulkan_lavapipe_provider.spl`, plus `artifact_store.spl`, `converter_graph.spl`, `converter_registry.spl`, `relation_engine.spl`, `matrix_compare.spl` |
| **Markdown projection** | **EXISTS as code** | `src/lib/common/spec/evidence/manual_render.spl`, `counterpart/manual_projection.spl`, `counterpart/evidence_projection.spl`; regeneration is gated — `regeneration_gate.spl:44` `render_manual_digest`, `:58` `assert_regeneration_stable`, `:85` `manifest_regeneration_report` |
| Typed **`EvidenceRequest`** | **DOES NOT EXIST as a type** | `grep 'struct EvidenceRequest\|enum EvidenceRequest'` over `src/**.spl` returns **zero**. The only hit is a *pipeline comment*: `model.spl:7` `#   EvidenceRequest -> provider -> RawArtifact -> format adapter` |
| **`EvidenceProvider`** trait | **DOES NOT EXIST as a type** | `grep 'trait EvidenceProvider\|class EvidenceProvider'` returns **zero**. `provider_runner.spl:7` is a comment: "This is the body of `CounterpartEvidenceProvider` (design §13)" — design-doc vocabulary, not a declared trait |
| **`EvidenceManifest`** | **DOES NOT EXIST in the spec layer** | The only manifest type is `MciEvidenceManifestV1` (`src/lib/nogc_sync_mut/mission_critical/mci_evidence_manifest_v1.spl:56`), a mission-critical artifact, not the spec evidence pipeline's |

**Honest summary (INFERRED from the above):** the research claim is **substantially true but
partly design-doc vocabulary**. Selectors, oracles, canonical evidence, format adapters, a
comparator, a provider *registry+runner* with nine concrete providers, and a gated Markdown
projection are all real code. The three nouns at the *ends* of the pipeline — a typed request
record, an abstract provider trait, and a spec-layer evidence manifest — are named only in
comments. That is exactly where SVAP's `TestIntent`, `ExecutionPlan`, and `EvidenceManifest`
must land, so this is a favourable starting position: **SVAP extends a real pipeline at its two
open ends, it does not replace it.**

There is also **MEASURED** a Markdown-projection extension surface
(`src/lib/common/spec/evidence/spipe_extension.spl:41-188`: `spipe_evidence_node`,
`spipe_evidence_extension`, `extension_lines`, `extension_is_wellformed`,
`extension_wellformed_reason`) and a legacy compatibility facade
(`evidence/legacy_facade.spl`, `evidence/untyped_capture.spl`).

### 2.3 The §11.8 "temporary capture code" — it is real and it is exactly where the plan said

**MEASURED.** `test/03_system/app/nvme_firmware/nvme_nand_capture_spec.spl:110` defines a
per-spec local helper `fn capture_bit_table(name, words, view, fields) -> bool`, used at `:151`
and `:180`. This is the hexdump-style local capture §11.8 orders replaced by shared providers.
It is one file, so the migration is small and concrete — a good first SVAP increment.

### 2.4 RISC-V core, debug, JTAG/DTM/DMI — what exists

**MEASURED.** Substantially more than "nothing", and less than "a production debug module."

| Thing | Status | Evidence |
|---|---|---|
| JTAG TAP | exists, **handwritten VHDL** | `src/lib/hardware/debug/jtag_tap.vhd`, `jtag_debug_chain.vhd` |
| RISC-V DTM | exists, handwritten VHDL | `src/lib/hardware/debug/riscv_dtm.vhd` |
| DMI bus | exists, handwritten VHDL | `src/lib/hardware/debug/dmi_bus.vhd` |
| Debug Module (v0.13) | exists, handwritten VHDL, staged | `src/lib/hardware/debug/riscv_debug_module.vhd:1-12` — header states Stage 3 abstract register access (DATA0/1, COMMAND, ABSTRACTCS), Stage 4 DM-resident `dpc`/`dcsr`, Stage 5 System Bus Access (SBCS/SBADDRESS0-1/SBDATA0-1, DMI 0x38..0x3D) |
| DM register block incl. SBA engine | exists | `src/lib/hardware/debug/debug_registers.vhd` |
| Hart glue | exists, **"stub-level GPR port toward the hart"** | `riscv_debug_module.vhd:5-7` (its own words) |
| Testbenches | exist | `tb_jtag_dtm_dmi.vhd`, `tb_debug_module.vhd`, `tb_abstract_cmds.vhd`, `tb_debug_csrs.vhd`, `tb_sba.vhd`, `tb_hart_integration.vhd`, `tb_soc_jtag_debug.vhd`, `tb_openocd_bitbang.vhd`, `tb_bscane2_bridge.vhd`, `tb_uart_bscan_log.vhd` |
| OpenOCD | exists | `src/lib/hardware/debug/openocd_riscv_sim.cfg`, `openocd_bitbang_glue.c`, `openocd_attach.md`; adapter `src/lib/nogc_sync_mut/dap/adapter/openocd.spl` |
| GDB | exists | `gdb_e2e.gdb`, `gdb_e2e.md`, `run_gdb_e2e.shs`, `run_hart_e2e.shs`, `run_native_gdb_hart.shs`; RSP/MI libraries under `src/lib/nogc_sync_mut/debug/` |
| Simple-side hart debug hooks | exists | `src/lib/hardware/debug_hooks/hart_debug.spl:53-204` — `hart_dbg_halt_req`, `resume`, `step_once`, `ndmreset`, `read_gpr`, `dpc`, trace enable/len/at, `hart64_debug_step` |
| Xilinx BSCANE2 bridge | exists | `bscane2_tap_bridge.vhd`, `bscane2_stub.vhd` |

So the research claim that "a JTAG TAP, DTM/DMI, debug module registers, system-bus access,
OpenOCD and GDB test infra already exist" is **MEASURED TRUE**. Three qualifications that
matter for G6, all measured:

1. **The RTL is handwritten, not generated.** These `.vhd` files sit in `src/lib/hardware/debug/`
   authored by hand (staged-header prose, `tb_*` siblings), not emitted by
   `src/lib/hardware/vhdl_gen/`. §10.1's rule "generated RTL is never hand-edited" is therefore
   **not yet satisfied for the debug subsystem**, and there are no source maps binding these
   nets to Simple/HWIR IDs.
2. **The hart binding is stubbed.** The DM's own header says "stub-level GPR port toward the
   hart" and "stub-level hart ports (pc_i/prv_i/ebreak_i in, dpc_o/step_o out)". §10.3's
   "bind halt/resume/reset/step to the *canonical* cores" is unstarted.
3. **The debug port is unconditionally open — this is the security hole, and it is measured.**
   `src/lib/hardware/debug/debug_registers.vhd:661` drives `dmstatus_v(7) := '1';` with the
   inline comment `-- authenticated (no auth unit)`, documented at `:20`
   (`version=2 (0.13), authenticated=1 (no auth)`). There is **no authentication unit, no
   `authdata` register, and no lifecycle state anywhere in the debug subsystem.** A part taped
   out with this RTL has an externally reachable, always-authenticated debug module with system
   bus access. §4.3 is the fix; §6.4 is the gate.

### 2.5 Product configuration and `rv32_nvme`

**MEASURED.** `CoreConfig` exists — `src/compiler/50.mir/hwir/types.spl:248` — but it is an
**HWIR strictness/validation config, not a product profile**. Its entire field set is
`xlen`, `physical_address_bits`, `register_count`, `profile`, `isa_profile`,
`compressed_decode_profile` (`:249-254`), validated by `diagnostic()` (`:256-283`) against a
closed list of ten scalar ISA profiles (`rv32i`, `rv64i`, `rv32im`, `rv64im`, `rv32i_zca`,
`rv64i_zca`, `rv32i_zmmul`, `rv64i_zmmul`, `rv32i_zicsr_zifencei`, `rv64i_zicsr_zifencei`) and
four compressed profiles. Presets are `rv32()` (`:289`), `rv64()` (`:293`),
`rv32_zca_integer()` (`:297`).

**It carries no atomics, no PMP/PMA, no debug, no trace, and no ECC/parity axis** — precisely
the five axes §10.2 requires of `rv32_nvme`. So `rv32_nvme` as a *product profile* is
greenfield, not an extension of `CoreConfig`.

**MEASURED**, the name `rv32_nvme` exists today only as testbench-generator identifiers and
gate scripts, never as a core configuration: `src/lib/hardware/vhdl_gen/generate_main.spl:23`
and `:100-101` (`generate_tb_rv32_nvme_fw_smoke`, `tb_rv32_nvme_fw_smoke.vhd`,
`generate_tb_rv32_nvme_bram_soc`), `src/lib/hardware/vhdl_gen/tb_single_lane_types.spl:2`, and
`scripts/check/check-rv32-nvme-host-axi-mmio.shs`, `scripts/check/check-rv32-nvme-nand-recovery.shs`.

### 2.6 The IR single-source layer — none of it exists

**MEASURED.** A case-insensitive scan of all `.spl` and `.sdn` under `src/` for each name
returns **zero files**:

`PinIR`, `PadIR`, `RegisterIR`, `MemoryIR`, `ProtocolIR`, `TestIntentIR`, `SVAP`,
`StimulusArtifact`, `BSDL`, `MBIST`, `ATPG`, `boundary_scan`.

(A `-i` scan for `STIL` returns four files — `src/lib/log.spl`, `src/lib/pure/autograd.spl`,
`src/lib/nogc_async_mut_noalloc/qemu/mod.spl`,
`src/lib/nogc_async_mut_noalloc/baremetal/riscv/startup.spl` — which are the English word
"still". **These are not STIL tooling and must not be cited as such.** STIL support is zero.)

**This is the most important measurement in this document.** Workstream G's IR layer, on which
§7.4's PinIR->ATE projection depends, is **entirely greenfield**. Workstream F must therefore
not assume PinIR and must define its own minimal `PadDecl` shim (§4.5) so F is not blocked
behind G — while binding to G's PinIR the moment it lands.

### 2.7 Existing gate vocabulary this workstream extends

**MEASURED**, `scripts/check/` already carries the RISC-V/NVMe gate family whose naming and
verdict style F must match: `check-riscv-hardware-gates.shs`,
`check-riscv-product-level-evidence.shs`, `check-riscv-formal-dual-track.shs`,
`check-riscv-rtl-truth.shs`, `check-riscv-rtl-sby-proof.shs`, `check-riscv-budget-evidence.shs`
(+ `-selfcheck`), `check-riscv-vivado-synth-evidence.shs`, `check-riscv-fpga-sidecar-contract.shs`,
`check-riscv32-riscv64-template-ownership.shs`, `check-riscv-gen2-zca-oracle.shs`,
`check-rv32-nvme-host-axi-mmio.shs`, `check-rv32-nvme-nand-recovery.shs`,
`check-nvme-firmware-remaining-gates.shs`.

### 2.8 Measured-state summary

| G6 ingredient | State |
|---|---|
| Typed evidence pipeline (selectors/oracles/adapters/comparator/providers/Markdown) | **exists as code**, extendable |
| `EvidenceRequest` / `EvidenceProvider` trait / spec `EvidenceManifest` | **comments only** |
| `TestIntent` / `ExecutionPlan` / SVAP pack | **does not exist** |
| JTAG TAP / DTM / DMI / DM v0.13 / SBA / OpenOCD / GDB | **exists**, handwritten VHDL, stubbed hart binding |
| Debug authentication / lifecycle | **does not exist**; `authenticated` hardwired `'1'` |
| `CoreConfig` | exists as HWIR strictness config; **no product axes** |
| `rv32_nvme` product profile | **does not exist** (name used for testbenches only) |
| PinIR / PadIR / RegisterIR / MemoryIR / BSDL / MBIST / STIL / ATPG | **zero** |
| Per-spec ad-hoc capture to be replaced | one site, `nvme_nand_capture_spec.spl:110` |

---

## 3. SVAP — the Simple Verification Artifact Pack

Everything in §3 onward is **PROPOSED** unless it cites a `file:line`.

### 3.1 Interchange format: SDN, overriding the research

The research (§11.1) specifies "canonical JSON/JSONL plus content-addressed binary blobs."
**This plan deliberately overrides that choice: SVAP's canonical interchange is SDN.** Reasons,
stated so the divergence is not silent:

- Project rule: config and data are SDN, never JSON/YAML.
- The repo's own tracking DBs are SDN (`doc/08_tracking/test/test_db.sdn`), and the SDN codec is
  first-party (`src/lib/common/sdn`), so there is no adapter to maintain.
- The property that actually matters — **content-addressing** — is format-independent. Every
  artifact is bound by SHA-256 in the manifest either way.

JSON is retained in exactly one place and only as an **export adapter**: `svap-export --json`
for third-party test-house tooling that cannot read SDN. That export is one-way, derived, never
read back, and never authoritative. Existing typed JSON evidence handling
(`evidence/format/json_document.spl`, **MEASURED**) is unaffected — it parses a DUT's JSON
output, which is a different concern.

```text
SVAP/
  manifest.sdn              # binds every file by sha256; schema/tool/profile versions
  schemas/*.sdn             # versioned record schemas
  intent/*.sdn              # TestIntent
  target/*.sdn              # target + fidelity profiles
  plan/*.sdn                # ExecutionPlan, one per (intent, target)
  stimulus/*.sdn|.bin       # StimulusArtifact
  schedule/*.sdn            # fault/power/event schedules
  oracle/*.sdn              # OracleArtifact
  coverage/*.sdn            # CoverageArtifact (intent) + CoverageResult (observed)
  trace/*.sdnl              # canonical trace, line-per-record SDN (see §3.5)
  pattern/*.sdn + blobs/    # imported external ATPG/STIL, origin: ExternalAtpg
  projection/*              # generated per-target content (STIL, SVF, XDC, testbench)
  result/*.sdn              # ComparisonResult, EvidenceManifest
  blobs/sha256/<digest>     # content-addressed payloads
```

### 3.2 The typed pipeline

```text
SSpec scenario (.spl, describe/it/step/expect — unchanged surface)
  └─ test_intent(...) builder            [NEW library API, §3.6]
       ↓
    TestIntent                           [NEW record]
       ↓  target-independent
    ScenarioGraph  (stimulus graph × oracle graph × schedule × coverage intent)
       ↓  per applicable target profile
    ExecutionPlan                        [NEW record]
       ↓
    StimulusArtifact + OracleArtifact + CoverageArtifact
       ↓
    runner  ──────────────────────────── one per projection (§3.4)
       ↓
    RawArtifact + CanonicalTrace
       ↓
    comparator  ← EXTENDS src/lib/common/spec/evidence/evidence_comparator.spl (MEASURED)
       ↓
    ComparisonResult + CoverageResult + EvidenceManifest
       ↓
    SVAP result pack (SDN + content-addressed blobs)
       ↓
    Markdown / dashboard projection ← EXTENDS manual_render.spl + regeneration_gate.spl (MEASURED)
```

**Authority rule (from §11.2, binding):** Markdown generation is strictly downstream and has no
authority to change an oracle. This is already half-enforced — `regeneration_gate.spl:58`
`assert_regeneration_stable` (**MEASURED**) proves the Markdown is a pure function of the
evidence; SVAP extends that gate to cover the whole pack.

### 3.3 Core records

Composition and traits only; no inheritance. Generics `<>`.

**`TestIntent`** — the canonical unit. One per `it` block that opts in.

```text
id: TestIntentId                     # stable, e.g. "riscv.debug.lifecycle.locked_denies_sba"
requirement_ids: [RequirementId]
source_span: SourceSpan              # file, line range
source_hash: Sha256                  # of the spec file text
purpose: IntentPurpose               # Functional | Structural | Parametric | Diagnostic
safety_class: SafetyClass
preconditions: [ResourceRequirement]
parameters: ParameterModel           # constraint model for random exploration
stimulus: StimulusGraph
oracles: [OracleRef]
schedule: ScheduleGraph
coverage_goals: [CoverageGoal]
fault_domains: [FaultDomain]
targets: [TargetProfileId]           # which projections apply
evidence_grade: EvidenceGrade        # Behavioral | Simulated | Rtl | Fpga | Silicon
```

**`ExecutionPlan`** — one per `(TestIntent, TargetProfileId)`.

```text
intent_id, target_profile, fidelity
ordering_policy, seed, exploration_bounds
image_hash: Sha256                   # firmware/bitstream/ELF identity
clock_reset_power_setup: PowerPlan
resource_bindings: [ResourceBinding]
stimulus_projection_ids, oracle_ids, comparator_id
capture_selectors: [EvidenceSelector]   # REUSES model.spl:48 (MEASURED)
timeouts, liveness_conditions
```

**`Stimulus`** — a closed enum (per §11.3), so an unhandled variant is a compile error rather
than a silent skip. Phase-1 subset relevant to G6, with the rest reserved:

```text
enum Stimulus:
    PinVector | ClockAction | ResetAction | PowerAction
    JtagAction | DebugAction | SfrAccess | AxiTransaction
    MemoryImage | FirmwareImage | FaultAction
    NvmeCommand | PcieTlp | QueueMemoryWrite | DmaAction
    OnfiCycle | NandMediaAction | HostCommand
```

**`Oracle`** — the §11.3 list. **Reuse, do not re-invent.** `OracleMode` /
`OracleCheck` / `OracleSpec` already exist (`model.spl:175-316`, **MEASURED**) covering Exact,
MaskedExact-by-selector, OrderedSequence, multiset, NumericTolerance, bind/same-as. SVAP adds
the temporal and relational modes that are missing: `Eventually`, `Never`, `TemporalWindow`,
`Invariant`, `Differential`, `Metamorphic`, `Distribution`, `CoverageThreshold`, `NoDataLoss`,
`ProtocolConformance`, `StateTransition`, `HashEquality`.

**Fail-closed rule, inherited from §11.3 and non-negotiable:** a missing or ambiguous selector
is a FAIL, never a skip and never a pass.

**`Schedule`** — named event boundaries, not cycle numbers, so one schedule survives
re-projection across fidelities:

```text
after(event("NandProgramAccepted")) and before(event("JournalCommitDurable"))
```

Each entry: virtual timestamp *or* named boundary, delta/phase, owner, preemption/fault choice,
happens-before constraints, repeat/termination.

**`EvidenceManifest`** — the record §2.2 found missing from the spec layer. Per EMU invariant
2.4 it names: source revision, compiler/tool versions, config hash, firmware/image hash, seed,
schedule hash, target identity, and the sha256 of every artifact. **INFERRED:**
`MciEvidenceManifestV1` (`mission_critical/mci_evidence_manifest_v1.spl:56`, **MEASURED**) is a
close structural precedent worth reading before designing this, but it is a different layer and
should not be extended in place.

### 3.4 One scenario, four (plus one) projections

This table is the concrete answer to G6.

| # | Projection | What is generated | Evidence grade | Buildable now? |
|---|---|---|---|---|
| P1 | **Ordinary host `bin/simple test`** | direct in-process typed actions against behavioral models; existing comparator + Markdown | Behavioral | **Yes** (§7 stage 1) |
| P2 | **Simulation (GHDL/Verilator testbench)** | clock/reset drivers, bus/pin transactions, assertions, waveform selectors | Rtl | Partly — GHDL tier blocked (§7.5) |
| P3 | **FPGA / board** | host control script + data, JTAG/UART/PCIe transactions, capture instructions, fixture procedure | Fpga | Partly (FPGA gates exist, §2.7) |
| P4 | **ATE functional** | digital pin groups, drive/sample vectors, timing sets, level sets, STIL functional projection, SVF for boundary-scan | Silicon | No — needs PinIR (§2.6) |
| P5 | *(import lane)* **External ATPG** | **nothing generated**; STIL/pattern artifacts imported, manifested, scheduled, executed, compared | Silicon | Import path buildable early |

P5 is drawn in the same table deliberately: it is the same campaign system, and putting it
anywhere else invites the confusion §1 forbids.

**What "the same scenario" means, precisely.** P1..P4 share the **TestIntent, the architectural
oracles, the named-event schedule, and the coverage goals**. They differ in the ExecutionPlan
and in *additional* tier-specific detail oracles. The comparator does **not** require cycle
equality between P1 and P2 (§11.9) — it requires the architectural oracles to hold in all
applicable tiers and the tier-detail oracles to hold in their own.

### 3.5 Traces

Control metadata is SDN. High-volume streams use **`.sdnl`** — one canonical SDN record per
line — with a header record carrying: magic, schema id, endianness, clock/time unit, record
type, field-dictionary hash, compression, record count, payload hash.

**Do not invent a compact binary format yet.** Per §11.4, a binary/zstd profile is added only
after the field semantics are stable and a differential test proves the binary and `.sdnl`
readers agree record-for-record.

Trace types required by §11.5. G6-critical subset first: `PinTrace`, `DebugTrace`,
`RetirementTrace` (RVFI/RVVI-compatible), `PowerTrace`, `SfrTrace`, `BusTrace`, `IrqTrace`,
`CoverageTrace`. NVMe/FTL/Media/Dma/Timing traces follow with workstreams D and E.

**Every trace transport reports emitted / captured / dropped / overflow counts** (§10.7). A
prefix must never be able to masquerade as a complete trace — a nonzero `dropped` or `overflow`
with an oracle that depends on completeness is a FAIL.

### 3.6 The ordinary-run projection: an upgrade path, not a parallel universe

**This is the section that decides whether G6 is real.** There are 21,510 `*_spec.spl` files
under `test/` (**MEASURED**). Any design requiring them to change is rejected on arrival.

Four rules:

1. **`describe`/`it`/`step`/`expect` remain exactly as they are.** No grammar change, no new
   spec runner, no new file extension, no migration of existing specs. A spec that never
   mentions SVAP behaves today, byte for byte, as it does now. This is §11.7's explicit
   instruction and it is load-bearing here.
2. **Opt-in is additive and local.** A spec becomes SVAP-projectable by adding a typed builder
   *inside* an existing `it`:

```simple
# @req REQ-RV32-DBG-011
it "denies system-bus access when the debug lifecycle is Locked":
    var t = test_intent("riscv.debug.lifecycle.locked_denies_sba")
    t.targets([Behavioral, FullRtl, Fpga, SiliconFunctional])
    t.stimulus(lifecycle_set(LifecycleState.Locked))
    t.stimulus(jtag_dmi_write(SBCS, sbreadonaddr: true))
    t.stimulus(jtag_dmi_write(SBADDRESS0, ProtectedAddr))
    t.oracle(never(event("SbaReadCompleted")))
    t.oracle(exact(selector_binary_field("dmstatus", lsb: 7, width: 1), "0"))
    t.cover(state_transition("lifecycle.ManufacturingTest->Locked"))
    t.capture([DebugTrace, BusTrace, PinTrace])
    expect(run_intent(t)).to_be_pass()
```

3. **`run_intent(t)` under `bin/simple test` executes the P1 projection in-process and returns
   an ordinary boolean/result the existing `expect` consumes.** No emulator, no simulator, no
   external tool, no network. It emits the SVAP pack as a side artifact under
   `build/svap/<intent_id>/`. **So the ordinary run is not a degraded mode — it is projection
   P1, and it is the default.** A developer who never thinks about ATE still gets a green test
   the normal way.
4. **`bin/simple test --svap-project <target>` re-projects the same intents** to P2/P3/P4/P5
   without executing them on the host, emitting only plans and stimulus/oracle artifacts for the
   downstream runner. Same source, same intent id, same oracles.

Migration of the one measured ad-hoc capture (§2.3): `capture_bit_table`
(`nvme_nand_capture_spec.spl:110`) is deleted and replaced by the shared provider
`capture_binary_layout`, which already has a natural home
(`evidence/format/binary_layout.spl`, **MEASURED**). Per §11.8 the shared provider set is
`capture_binary_layout`, `capture_transaction_stream`, `capture_signal_trace`,
`capture_pin_vectors`, `capture_memory_image`, `capture_timing_timeline`, `capture_coverage`.
**A capture with no oracle and no manifest entry cannot pass** — that rule is what makes the
deletion safe rather than a loss of coverage.

---

## 4. DFT and manufacturing hooks

### 4.1 The §10.9 content-source table, made buildable

| Test content | Source | Simple owns | Test house owns | Prereq |
|---|---|---|---|---|
| Functional boot/protocol/pin scenarios | SSpec `TestIntent` -> P4 projection | intent, stimulus, oracles, vectors, timing-set *input*, scheduling, comparison, evidence | tester program assembly, load boards, final timing/level closure, binning | PinIR (§2.6 zero) |
| Boundary-scan connectivity | PinIR/PadIR -> BSDL + generated sequences | pad/pin model, BSDL **inputs**, connectivity intent, SVF sequences, result comparison | BSDL sign-off against the real pad ring, fixture, continuity limits | PinIR (zero), BSDL generator (zero) |
| MBIST algorithms + expected status | MemoryIR + selected March algorithm | memory inventory, algorithm selection, launch/status procedure, repair-status decode, evidence | BIST controller IP if third-party, repair fuse blow, yield rules | MemoryIR (zero) |
| **Scan stuck-at / transition ATPG** | **external ATPG on scan-inserted netlist** | **import, manifest, schedule, execute, compare, trace — nothing else (§1)** | **pattern generation, fault grading, coverage numbers, scan insertion, netlist** | ATPG tool + netlist (neither in repo) |
| Parametric / electrical (IDDQ, leakage, VIL/VIH, Fmax shmoo) | tester/lab methods | referencing them from the common manifest; consuming their results as evidence | the tests themselves, limits, correlation | none — reference-only from day 1 |

**The ownership line, stated once:** Simple owns **intent, campaign orchestration, scheduling,
comparison, evidence, and results** across all five rows. Simple owns **content generation** only
in rows 1-3. Simple owns **nothing** of row 4's content and **nothing** of row 5's methods.

### 4.2 Source-level DFT contracts (§10.9)

Declared once in SDN, projected to RTL top-level integration, firmware accessors, and test
content: scan enable / test mode / clock override; MBIST launch and repair status; optional
logic-BIST hooks; JTAG boundary scan and BSDL inputs; IEEE 1687/IJTAG instrument network and
procedures; clock/reset test controls; analog/mixed-signal observation hooks; fuse/OTP
provisioning and readback policy; the secure manufacturing-test lifecycle (§4.3).

**Rule:** none of these is hand-written at the top level. §10.1's "generated RTL is never
hand-edited" applies; where the debug RTL is currently handwritten (§2.4), the DFT integration
must be generated even while the DM itself is not, and the boundary between them recorded.

### 4.3 Debug/trace security lifecycle — the measured hole and its fix

**The hole (MEASURED):** `debug_registers.vhd:661` drives `dmstatus.authenticated := '1'`
unconditionally, commented `-- (no auth unit)`. There is no `authdata` register, no challenge
flow, no lifecycle state. Combined with the live SBA engine (DMI 0x38..0x3D,
`riscv_debug_module.vhd:9-12`), a production part built from this RTL exposes authenticated
system-bus access over JTAG to anyone with physical access.

**The fix.** Lifecycle states per §10.4, with an explicit permission matrix, machine-readable in
`rv32_nvme.dft.sdn`:

```text
Development -> Provisioning -> ManufacturingTest -> FieldDiagnostic -> Locked
```

| State | JTAG/DTM | Auth required | Invasive debug | Trace | SBA | Unlock |
|---|---|---|---|---|---|---|
| Development | open | no | yes | full | yes | n/a |
| Provisioning | open | yes | yes | full | yes | key install |
| ManufacturingTest | open | yes (test-house key) | yes | full | yes | fuse-gated |
| FieldDiagnostic | open | yes | **non-invasive only** | filtered by address | **no** | signed challenge, audited |
| **Locked** | **DTM answers IDCODE only** | — | **no** | **crash-dump path only** | **no** | **none (permanent fuse)** |

Design rules, each individually testable:

- `dmstatus.authenticated` becomes a **function of lifecycle state and an `authdata`
  challenge/response**, never a constant. Deleting the constant `'1'` is the first RTL change.
- **Debug SBA must not bypass PMP/PMA or security policy in Locked/FieldDiagnostic** (§10.3).
  The SBA master is routed through the same protection check as a hart access.
- The **crash-dump / bounded retirement-trace path survives Locked** (§10.3 last bullet) — a
  locked part is still diagnosable post-mortem without being interactively debuggable.
- **Every unlock produces an audit record** that enters attestation and the SVAP
  `EvidenceManifest`. The lifecycle state at test time is part of the evidence, not an ambient
  condition.
- Permanent disable is a **fuse**, one-way; the RMA policy is declared alongside it, not implied.

Gate: §6.4.

### 4.4 Production debug module work (§10.3)

Ordered by dependency, each item measurable against §2.4's stub state:

1. Replace the stub GPR/CSR ports with binding to the canonical RV32/RV64 architectural files.
2. Bind halt/resume/reset/step to the real hart (today `hart_debug.spl` hooks exist on the
   Simple side, **MEASURED** `:53-138`; the RTL side is stubbed).
3. Program-buffer execution; system-bus access sizes required by OpenOCD/GDB.
4. Native `stepi`; software and hardware breakpoints; execution / load-store / address-data /
   privilege triggers.
5. Per-hart and group halt/resume; reset-halt and first-instruction halt; defined
   unavailable/nonexistent-hart behaviour.
6. Precise debug entry around exceptions, interrupts, WFI, and speculation.
7. §4.3's authentication and lifecycle gating.
8. Source maps binding every debug RTL process/net/register to Simple/HWIR IDs (§10.1) — the
   prerequisite for the handwritten RTL ever becoming generated.

**The existing fake-hart GDB session remains a protocol test, not real-core completion
evidence** (§10.3, verbatim). The gate in §6.3 encodes exactly that distinction.

### 4.5 PinIR dependency and the un-blocking shim

PinIR/PadIR is workstream G's and is measured at zero (§2.6). To keep F unblocked, F defines a
**minimal `PadDecl` shim in SDN** covering only what the ATE projection needs — logical function,
package ball, direction, voltage domain, safe reset value, differential mate, test-mode
ownership — and **binds to G's PinIR the moment it lands, deleting the shim**. The shim is
explicitly temporary and carries a `superseded_by: PinIR` field so it cannot quietly become a
second source of truth. **This is the one place F is permitted to duplicate G, and only under
that field.**

---

## 5. The `rv32_nvme` product configuration

**PROPOSED.** A product profile is a new record, not an extension of `CoreConfig` (§2.5 —
`CoreConfig` validates HWIR strictness and has none of the required axes). Declared in
`rv32_nvme.product.sdn`; every field must resolve to implementation *and* evidence before
release (§10.10 bullet 1).

```text
product: rv32_nvme
role: "SSD controller firmware core"

isa:
  base: rv32i
  extensions: [m, a, c, zicsr, zifencei]     # atomics REQUIRED by §10.2
  compressed_profile: zca-integer-rv32       # matches CoreConfig (types.spl:297)

memory_protection:
  pmp_regions: 16
  pma: declared                              # cacheability/idempotency/atomicity per region

debug:
  dm_version: "0.13"
  sba: true
  triggers: [exec, load_store, addr_data, privilege]
  lifecycle: rv32_nvme.dft.sdn#lifecycle     # §4.3 — NOT optional

trace:
  retirement: rvfi                           # RVFI/RVVI-compatible RetirementTrace
  buffers: bounded
  loss_reporting: required                   # §10.7 — dropped/overflow always reported

integrity:
  regfile: parity
  caches: ecc
  injection_reaches_software: required       # §10.10

verification_matrix: rv32_nvme.verify.sdn    # closed matrix, §5.1
```

`CoreConfig` (`types.spl:248`) remains what it is — the HWIR strictness config. The product
profile **references** it (`isa.base` + `isa.compressed_profile` must satisfy
`CoreConfig.diagnostic()`), and the two must never diverge; §6.5 gates that.

### 5.1 Differential architectural verification (§10.5)

No single suite is sufficient; the closed matrix requires all six lanes, each with a distinct
failure mode:

| Lane | Role | Repo starting point |
|---|---|---|
| ACT4 self-checking ELFs, driven by the exact UDB profile | architectural certification | none measured |
| Independent ISA model (Sail / Spike / Whisper) retirement diff | catches decode/semantic divergence | none measured |
| `riscv-dv` constrained-random streams | privilege, exceptions, MMU, debug | none measured |
| RVFI / riscv-formal | base-ISA + project formal properties | `check-riscv-formal-dual-track.shs`, `check-riscv-rtl-sby-proof.shs` (**MEASURED**) |
| RVVI-style retirement/event comparison | async interrupts, debug entry/exit | none measured |
| Directed SSpec scenarios (SVAP intents) | microarchitectural + SoC behaviour | this plan |

**ACT4 is a certification suite, not a processor-verification replacement** (§10.5, verbatim).
The release gate requires differential, random, formal, and implementation evidence *in
addition*.

### 5.2 Optimized-feature verification (§10.6)

`rv32_nvme` is a small in-order core, so the OoO/vector sections of §10.6 do not apply to it.
What does apply and must be covered: compressed 16/32-bit alignment and exceptions at
fetch/decompress boundaries; `FENCE`/`FENCE.I`/aq-rl/AMO/LR-SC; self-modifying code and
DMA-to-executable-memory invalidation; PMP/PMA checked **before** side effects; unaligned access
and atomicity policy; ECC/parity correctable and uncorrectable paths reaching software-visible
recovery; cache/TLB reset and power-domain behaviour; and no wrong-path architectural or MMIO
side effect.

Per §10.6: **generate large datasets and result hashes rather than embedding expected arrays in
handwritten tests.** `HashEquality` (§3.3) exists for exactly this.

---

## 6. Release gates

All gates follow the repository convention exactly:

- Verdict is the **last line of stdout**: `PASS — <n> <things> checked, ...` (exit 0) /
  `FAIL — ...` naming every offender (exit 1) / `ERROR — nothing was checked (<reason>)` (exit 2).
- **Non-vacuity is absolute.** A run that checked **0** things is **ERROR, never PASS**. A
  missing tool, a missing artifact, an unreadable profile: all ERROR. Absence of evidence is
  never evidence.
- **`--selftest` runs before every scan and is fatal.**
- Exit status is read **directly into a variable on the line after the invocation, never through
  a pipe** — a pipeline's `$?` is the last command's status and has produced false greens in this
  repo before.
- Every gate has a **named sabotage** that must turn it red. A gate with no proven sabotage is
  not a gate.
- **No gate name may contain a claim §1 forbids.**

All scripts are `.shs`; all logic they invoke is `.spl`. None is written by this document.

### 6.1 `check-svap-pack-integrity.shs`

Checks every SVAP pack under `build/svap/`: manifest sha256 matches every file; every
`TestIntent` resolves to ≥1 `ExecutionPlan`; every plan names a comparator; every oracle names a
resolvable selector (ambiguous ⇒ FAIL, §3.3); every result names source rev, tool versions,
config hash, image hash, seed, schedule hash, target identity (EMU 2.4).
`PASS — <n> pack(s) checked, <m> artifact digests verified`.
**Sabotage:** flip one byte in a trace blob without updating the manifest ⇒ FAIL naming the file.
**Selftest fixtures:** clean pack PASS; digest mismatch FAIL; intent with no plan FAIL; oracle
with dangling selector FAIL; empty pack directory ⇒ 0 checked ⇒ ERROR.

### 6.2 `check-svap-projection-parity.shs`

For every intent declaring ≥2 targets, asserts the projections share intent id, requirement ids,
architectural oracle set, and schedule hash; and that tier-specific oracles are strictly
*additive*. This is the gate that makes "one scenario, two projections" checkable rather than
aspirational.
**Sabotage:** weaken one architectural oracle in the ATE projection only ⇒ FAIL naming the intent
and the dropped oracle.

### 6.3 `check-riscv-debug-real-hart.shs`

Requires GDB/OpenOCD debug tests against the **canonical hart**, not the fake-hart protocol
session. Halt/resume/step/reset, GPR/CSR read-write, breakpoints, triggers, SBA sizes.
**A fake-hart-only run is ERROR, not PASS** — that is the entire point of the gate, and it is
honestly RED today (§2.4: the DM header itself says "stub-level GPR port toward the hart").
**Sabotage:** point the harness at the fake hart ⇒ ERROR (not a silent pass).

### 6.4 `check-riscv-debug-lifecycle-locked.shs`

The security gate for §4.3. In `Locked`: DTM answers IDCODE only; `dmstatus.authenticated`
reads 0 without a valid challenge; SBA is denied; invasive debug is denied; the crash-dump path
still works; the unlock audit record is present in the manifest.
**Honestly RED today.** `debug_registers.vhd:661` hardwires `authenticated := '1'` with no auth
unit, so this gate fails on `main` the day it lands. That is the correct outcome: it is landed
**ADVISORY**, exactly as `check-stage-binaries-runnable.shs` was, and **promoted to MANDATORY
when §4.3 lands and it goes green.** Do not land it green by weakening it.
**Sabotage:** re-hardwire `authenticated := '1'` ⇒ FAIL naming the file and line.

### 6.5 `check-rv32-nvme-profile-closure.shs`

Every advertised item in `rv32_nvme.product.sdn` resolves to implementation **and** evidence;
`isa.base` + `isa.compressed_profile` satisfy `CoreConfig.diagnostic()`
(`types.spl:256`, **MEASURED**); the verification matrix is closed (no lane unpopulated); no
capability bit is advertised without a passing evidence row.
**Sabotage:** advertise `zbb` with no implementation ⇒ FAIL naming the unbacked capability.

### 6.6 `check-svap-nonvacuity.shs`

§11.11, mechanized. For each executed pack: ≥1 intended stimulus reached the DUT; the **DUT, not
the harness**, produced the observed response; required state transitions occurred; no capture
overflow or truncation (§3.5 counters); a **timeout is never a pass**; disabling the relevant DUT
path turns the test red; **a fixture literal cannot satisfy a live-capture oracle.**
**Sabotage (two required):** (a) stub the DUT response with the expected literal ⇒ FAIL;
(b) truncate a trace ⇒ FAIL on the overflow counter.

### 6.7 `check-svap-atpg-claim-hygiene.shs`

§1, mechanized. Scans gate names, SVAP capability bits, and workstream F/G docs for forbidden
claim forms; asserts every artifact with `origin: ExternalAtpg` has `coverage_authority:
external_tool` plus tool name and version, and that **no code path constructs an `ExternalAtpg`
artifact**.
**Sabotage:** add a gate named `check-...-generates-scan-patterns.shs` ⇒ FAIL naming it.

### 6.8 Full §10.10 release checklist (gate coverage map)

| §10.10 requirement | Gate |
|---|---|
| Advertised ISA/profile items resolve to implementation + evidence | 6.5 |
| Real-hart GDB/OpenOCD debug tests pass | 6.3 |
| ACT4 + differential/random/formal campaigns pass | §5.1 lanes; formal partly via `check-riscv-formal-dual-track.shs` (**MEASURED**) |
| RVFI/RVVI/trace interfaces non-vacuous | 6.6 |
| Optimized-feature mutants detected | mutation lane, §5.2 |
| Pin/reset/clock packs pass in RTL and FPGA | 6.2 (P2/P3), needs PinIR |
| CDC/RDC/reset clean or formally waived | external, referenced by manifest |
| ECC/parity injection reaches software-visible recovery | §5.2 + 6.5 evidence row |
| Synthesis/STA/power/resource envelopes | `check-riscv-vivado-synth-evidence.shs`, `check-riscv-budget-evidence.shs` (**MEASURED**) |
| DFT/MBIST/boundary-scan deliverables generated + validated | §4.1 rows 2-3, needs MemoryIR + PinIR |
| Security lifecycle disables/authenticates invasive debug | 6.4 |
| All evidence bound to source/RTL/bitstream/tool hashes | 6.1 |

---

## 7. Staged increments

Each stage states what it can prove and what blocks it. Stage N+1 does not start on faith that
stage N "basically works" — it starts on stage N's green gate.

### Stage 1 — SVAP core records + the P1 ordinary-run projection *(buildable now, no blockers)*

Build `TestIntent`, `ExecutionPlan`, `Stimulus`, the missing oracle modes, `EvidenceManifest`,
the SDN codec, and `run_intent()` executing in-process under `bin/simple test`. Reuse
`EvidenceSelector`/`OracleCheck` (`model.spl`, **MEASURED**) rather than re-declaring them.
Land `check-svap-pack-integrity.shs` and `check-svap-atpg-claim-hygiene.shs`.
**Proves:** a scenario yields a green ordinary test *and* a content-addressed pack.
**Does not prove:** anything about hardware.

### Stage 2 — replace the ad-hoc capture; land the shared providers *(buildable now)*

Delete `capture_bit_table` (`nvme_nand_capture_spec.spl:110`, **MEASURED**); implement the seven
§11.8 providers on the existing format adapters. Land `check-svap-nonvacuity.shs`.
**Proves:** captures cannot pass without an oracle and a manifest entry.

### Stage 3 — debug lifecycle design + the RED gate *(buildable now; gate lands ADVISORY)*

Author `rv32_nvme.dft.sdn` lifecycle and permission matrix; land
`check-riscv-debug-lifecycle-locked.shs` **ADVISORY and honestly RED**, with the sabotage proof.
**Proves:** the §2.4 security hole is now visible and ratcheted rather than latent.
**Blocked:** going green needs the RTL change (Stage 5).

### Stage 4 — `rv32_nvme` product profile + closure gate *(buildable now)*

`rv32_nvme.product.sdn` and `check-rv32-nvme-profile-closure.shs`. Expect an initially small
closed set — the point is that it is *closed*, not that it is large.

### Stage 5 — production debug module + auth unit *(needs RTL work; not blocked by bootstrap)*

§4.4 items 1-7. Removes the `authenticated := '1'` constant; binds the real hart; routes SBA
through protection. Promotes 6.4 to MANDATORY and turns 6.3 from ERROR to PASS.

### Stage 6 — P2 simulation projection *(BLOCKED — bootstrap redeploy)*

The GHDL and QEMU tiers are blocked behind the bootstrap redeploy failure reported by the master
plan as **`refusing non-production Simple runtime`**. **INFERRED / not fully verified:** a
repo-wide grep for that exact string under `src/` and `scripts/` did not complete within the
time budget, and the nearest matching tracked record found was
`doc/08_tracking/bug/shellout_specs_target_refusing_production_wrapper_2026-08-17.md`. Treat the
string as **reported by the master plan and inherited here**, and confirm the owning bug record
before acting on it. Independently corroborating: `check-stage-binaries-runnable.shs` is
documented as honestly RED with all four tracked stage binaries SEGV-ing, whose repair "needs a
bootstrap redeploy, which is blocked separately."
**Do not attempt to route around this by falling back to the Rust seed** — that violates the
default-tooling rule and would produce evidence of the wrong provenance.

### Stage 7 — P3 FPGA/board projection *(partly buildable)*

FPGA gates exist (§2.7). Board evidence bar per `.claude/rules/board-runnable.md`: board
identity + download/boot path + serial or SSH transcript. **QEMU-only is a defect, not a
completion.**

### Stage 8 — P4 ATE functional projection *(BLOCKED on PinIR)*

Needs workstream G's PinIR/PadIR (measured zero, §2.6) or the §4.5 shim. Produces pin groups,
timing-set input, STIL functional and SVF content. **Generates functional vectors only** (§1).

### Stage 9 — P5 external ATPG import lane *(import path buildable early; content external)*

Import STIL/pattern artifacts with `origin: ExternalAtpg`, manifest them, schedule, execute,
compare, trace. **No generation, ever.** This stage can be prototyped before Stage 8 using a
synthetic imported pattern file, because the import path is independent of PinIR.

### Dependency summary

```text
Stage 1 ─┬─ Stage 2 ── Stage 6 (BLOCKED: bootstrap redeploy)
         ├─ Stage 3 ── Stage 5 ── Stage 7 (board evidence bar)
         ├─ Stage 4 ─────┘
         └─ Stage 9 (independent)
                        Stage 8 (BLOCKED: PinIR, workstream G)
```

---

## 8. Interfaces to sibling workstreams

| Workstream | F consumes | F provides |
|---|---|---|
| **G** (IR single source) | PinIR/PadIR, RegisterIR, MemoryIR, ProtocolIR — **all measured zero** | the consumer requirements that make PinIR's ATE-projection fields concrete; the §4.5 shim, to be deleted on arrival |
| **A** (offload partition) | the 3-way equivalence gate's vector sets | `Differential` and `HashEquality` oracles; SVAP packs as the equivalence gate's evidence format |
| **E** (emulation build-out) | machine plane, ISA tier, the bootstrap unblock (Stage 6) | ExecutionPlan as the emulator's entry contract; `RetirementTrace`/`TimingTrace` schemas |
| **D** (NVMe completeness) | real payload/OOB/ECC widening | `NvmeCommand`/`NvmeTrace` stimulus and trace types |
| **H** (typed firmware model) | build modes and safety profiles | `safety_class` and `evidence_grade` on every intent |

---

## 9. What this plan does not claim

Stated plainly, because §11.3 of the master plan exists precisely to stop a workstream quietly
widening its own claims:

- It does not claim SSpec generates scan patterns, computes fault coverage, or replaces ATPG
  (§1).
- It does not claim the existing evidence pipeline is SVAP. It measured that three of the
  pipeline's named nouns are comments (§2.2).
- It does not claim `CoreConfig` is a product profile (§2.5).
- It does not claim any IR from §7 exists (§2.6).
- It does not claim the debug subsystem is production-ready. It measured that the hart binding is
  stubbed and `authenticated` is hardwired to 1 (§2.4).
- It does not claim a QEMU or simulation result is board evidence (Stage 7).
- It does not claim any gate in §6 is green. Two are specified as honestly RED on landing (6.3,
  6.4), and none exists yet.
