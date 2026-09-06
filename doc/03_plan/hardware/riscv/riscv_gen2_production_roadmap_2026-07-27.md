# Simple RISC-V — Completed Tasks and `riscv_gen2` Production Roadmap

Date: 2026-07-27
Status: **planned; Wave 0 not started**
Research: `doc/01_research/domain/riscv_gen2_production_audit_2026-07-27.md`
Supersedes for gen2 scope: `riscv32_riscv64_fpga_simpleos_production.md` (2026-07-18)
remains authoritative for the V1 Linux-bring-up lane.

---

## Part 1 — Completed tasks (state as of 2026-07-27)

### 1.1 VHDL exec-core generator — silicon-proven

`src/lib/hardware/vhdl_gen` (pure Simple) emits all six rv32/rv64 core variants
byte-identical to the checked-in goldens, parameterized by `XlenConfig` with an
AOP debug-tap aspect. KV260 booted SimpleOS from **generated-core** bitstreams.

### 1.2 KV260 silicon milestones

All four passed on real hardware: rv32-DDR, rv32 tiny-BRAM (no FSBL), rv64-DDR,
and NVMe firmware on the rv32 core, plus a green release gate. Durable crt0
`.bss`-zero landed with ELF-derived bring-up offsets.

Known open: tiny-BRAM SoC runs firmware twice per reset (bug `af4dfe99cf8`).

### 1.3 JTAG-terminal console and serial-base completeness — landed 2026-07-27

The console transport is now **configurable** rather than hard-wired per SoC
variant, and the JTAG path is proven cable-free on silicon.

| Deliverable | File |
|---|---|
| Console config (`uart`/`jtag`/`both`, `buf_words`), obs-command encoding, log parser, decoder with completeness verdicts | `src/lib/hardware/fpga_k26/jtag_console.spl` |
| 20-example completeness spec | `src/lib/hardware/fpga_k26/test/jtag_console_spec.spl` |
| Host entry point; non-zero exit on incomplete transcript | `src/app/jtag_console/main.spl` |
| `CONSOLE_MODE` / `BUF_WORDS` knobs; decode routed through the tested Simple path | `scripts/fpga/read_rv32_tiny_bram_obs.shs` |
| Operator guidance | `doc/07_guide/hardware/fpga/simpleos_on_simple_riscv_fpga.md` |

**Two console transports, selectable:**

- `CONSOLE_JTAG` (default) — every soft-UART TX byte is captured on-chip in the
  `UARTBUF_WORDS` buffer and read back over the **same FT4232H JTAG chain that
  programs the board**, through the BSCANE2 USER4 observation DR. Zero extra
  cabling. Capacity = `buf_words * 4` bytes (default 8 KB).
- `CONSOLE_UART` — PMOD J2 (H12 tx / E10 rx, LVCMOS33, 115200 8N1). Unbounded
  streaming, but requires a **3.3V USB-TTL cable** — never 5V, never RS-232.

**Defects found and fixed.** The prior readout was silently lossy three ways:
it capped the word loop at 8192 and printed the prefix as if whole (so an
overrun vanished); it dropped every byte `< 0x20` that was not `\n`; and it
emitted no verdict and no non-zero exit. The RTL was correct — it stops writing
at capacity but keeps counting, so loss was *detectable*, merely unreported.

**Board evidence 2026-07-27:** tiny-BRAM bitstream programmed; obs status
`magic=0x51f0b007`, `status=0xa1000238` (568 bytes, pass bit set), cycle counter
advancing across reads; full SimpleOS RV32 boot transcript recovered over JTAG
alone, ending `TEST PASSED`; verdict `COMPLETE: emitted=568 captured=568
lost=0`, script exit 0. 568 matches the documented GHDL tiny-lane baseline.
`CONSOLE_MODE=uart` exits 2 with cable instructions.

**Attribution caveat:** `bin/simple` is currently the Rust **bootstrap seed**
(seed warning banner present), not the self-hosted binary. This evidence is
seed-attributed. Re-run on a redeployed self-hosted binary before citing it in a
release gate.

### 1.4 Defects filed this session

- `doc/08_tracking/bug/lint_coll006_false_positive_integer_accumulator_2026-07-27.md`
  — COLL006 "string concat in loop" fires on integer accumulators (`i = i + 1`),
  making `simple lint` red across the whole hardware tree and turning the
  test-runner's post-spec lint gate into a phantom failure. Reproduced on
  untouched, silicon-proven sources as a control.
- Pre-existing and already tracked:
  `test_runner_post_spec_lint_gate_empty_file_arg_2026-07-20.md`.

### 1.5 Not done — carried into Wave 0

`k26_ddr` SoC has no capture buffer (PMOD-only console); adding it is a
generator + golden-regeneration change.

---

## Part 2 — Production roadmap

### 2.0 Evidence rules (inherited, non-negotiable)

The 2026-07-18 plan's rules carry forward unchanged, plus:

8. **Textual golden identity is not correctness evidence.** A golden proves the
   emitter is reproducible. ISA correctness requires differential, random, and
   formal evidence.
9. **No capability may be inferred from a directory name.** Every extension
   claim resolves through a machine-readable manifest to implementation files,
   specs, compliance evidence, and synthesis evidence.

### 2.1 Target architecture

```
FRONTEND
 ┌──────────┐   ┌──────┐   ┌────────┐   ┌────────────┐   ┌────────────┐
 │ Next PC  │──▶│ ITLB │──▶│ I-cache│──▶│ Fetch queue│──▶│16/32 align │
 │ + BPU    │   └──────┘   └────────┘   └────────────┘   │+ decompress│
 └──────────┘                                            └─────┬──────┘
                                                    ┌──────────▼──────────┐
                                                    │ N-way decode + uopQ │
                                                    └──────────┬──────────┘
                                                  BackendContract
                              ┌──────────────────────────┴──────────────────────────┐
                     IN-ORDER BACKEND                                        OoO BACKEND
              scoreboard / bypass / issue                          rename / PRF / ROB
              completion / precise commit                          IQ / LSQ / checkpoints
                              └──────────────────────────┬──────────────────────────┘
       ┌──────────┬───────────┬───────────┬──────────────┼──────────┬────────┐
       │ Integer  │ Branch    │ MUL/DIV   │ CSR/Trap     │ FP       │ Vector │
       └──────────┴───────────┴───────────┴──────────────┴──────────┴────────┘
                                                        │
                                              LSU / store buffer
                              ┌─────────────────────────┴──────────────────┐
                       write-back D-cache                             MMIO path
                              │                                            │
                        DTLB/PMP/PMA ──────────▶ L2 / fabric / AXI ◀───────┘
```

**Frontend/backend contract** — the frontend must not know which backend is
selected. Contracts: `DispatchBundle`, `Redirect`, `Completion`, `CommitBundle`,
`FlushEvent`, `MemoryRequest`. The in-order backend satisfies the same contract
with a small completion queue instead of a ROB.

**Backend selection is compile-time, not runtime.** A runtime switch would keep
both backends in silicon, cost area and timing, and multiply validation states.
A `serialize_mode` debug knob may force single-instruction execution without
removing either backend.

**Four distinct flush mechanisms** — do not conflate them: pipeline redirect
(branch/exception/interrupt), store-buffer drain (FENCE), instruction-fetch
synchronization (FENCE.I), and D-cache maintenance (CBO.CLEAN/FLUSH/INVAL).

### 2.2 Compiler path

```
Simple hardware source → typecheck/HIR/host-time elaboration → static hardware DI
  + structural aspects → typed Hardware IR → legality/width/clock/reset/memory-port
  validation → compile-time specialization → RTL process/netlist IR
  → deterministic VHDL-2008 emitter
```

- `--backend=vhdl --hardware-strict` uses the canonical HWIR path **only**. A
  failed lowering is an error, never a silent fallback. The current text/subset
  generator becomes `--backend=vhdl-legacy`.
- CI fails `riscv_gen2` sources containing raw semantic VHDL (`architecture`,
  `process(clk)`, `std_logic_vector(...)`, `when "..." =>` decode bodies). The
  only textual escape is a typed `BlackBox` for PLLs, SRAM macros, DSP
  primitives, clock-gating cells, and technology I/O — with declared ports,
  clock domains, side effects, latency, and simulation model.
- Widths use arbitrary-precision `Bits`/`BitVectorLiteral`, never signed host
  `i64` (see verified finding 4).
- **Hardware DI is elaboration-time**, distinct from runtime software DI:
  `interface → provider → module elaboration → instance + nets`. Scopes:
  `per_hart`, `per_core`, `per_cluster`, `shared_soc`, `compile_only`.
- One `CoreConfig` drives specialization; ≥85–90% of scalar source shared
  between RV32 and RV64. No runtime XLEN multiplexer in generated RTL.

**Declarative ISA database** replaces hand-coded decode, generating scalar
decode tables, compressed decompression, illegal checks, disassembler metadata,
coverage points, profile/UDB capability data, and differential-test mappings
from one source.

### 2.3 MDSOC+ boundary

MDSOC+ governs ownership, composition, dependency direction, and elaboration.
**No dynamic message or service lookup on decode, issue, wakeup, bypass, or
cache-hit paths** — those stay typed wires and ready/valid protocols. Capsules:
`hardware.{elaboration,ir,backend.vhdl}`, `riscv.{profile,isa,uop,frontend,
backend.contract,backend.inorder,backend.ooo,execute.scalar,execute.fp,
execute.vector,memory,privilege,interrupt_debug,soc,verification,release}`.

### 2.4 Waves

| Wave | Scope | Exit gate |
|---|---|---|
| **0 — Truth reset** | Freeze V1 as `legacy_riscv_v1`; record all FPGA/GHDL evidence; machine-readable capability manifests; reclassify inaccurate `gc` claims; **red** specs for every verified blocker | No feature appears in documentation without an implementation path and test evidence |
| **1 — Compiler foundation** | HWIR v1; hardware DI graph; clock/reset + memory-port concepts; strict VHDL mode; deterministic generation + source maps; fallback removed from certified builds | A Simple hardware module lowers through HWIR to synthesizable VHDL with no raw VHDL semantics |
| **2 — Shared scalar core** | Shared RV32/RV64 datapath; complete I and M; profile-aware C decompressor; strict illegal handling; **real ECALL/EBREAK traps**; CSR semantics; external I/D interfaces; RVFI retire | RV32+RV64 scalar tests pass through generated VHDL with Sail differential evidence and nonzero retirement |
| **3 — In-order frontend + memory** | Two-wide frontend/decode; predictor/BTB/RAS; I-cache; write-back D-cache; store buffer; FENCE/FENCE.I/CBO; A extension + RVWMO; timer/software/external interrupts | Dual-issue core runs realistic embedded workloads with branch/cache counters and no deadlock |
| **4 — RVA22S64 scalar** | F, D, Zfhmin; Zba/Zbb/Zbs; profile cache ops + misaligned access; Sv39, TLB, PTW, PMP/PMA; supervisor traps/delegation; OpenSBI + DT + Linux; coherent fabric interface | Manifest closes every mandatory RVA22S64 item; OpenSBI and Linux reach a deterministic userspace milestone |
| **5 — OoO backend** | Three-wide rename/dispatch/commit; PRF + free list; ROB; IQ; LSQ + replay; branch checkpoints; precise exceptions; speculative-load restrictions | Traces match the in-order reference under directed and random tests; formal proves no wrong-path architectural side effects |
| **6 — Vector** | RVV 1.0 decode/state; VRF; vector execution + LSU; vstart/masking/tails/reductions/permutations; precise vector traps and fault-only-first; 128-bit datapath | RVA22S64+V manifest complete; Sail differential covers vector state and memory faults |
| **7 — Production closure** | Debug/JTAG; ECC/parity; error injection; CDC/RDC/reset; optional AIA; optional multicore/coherence; security review; synthesis + STA closure; release provenance/SBOM; DFT/MBIST hooks | Full production definition-of-done met |

**Speculation rules from Wave 5 on.** Permitted: speculative branch execution,
speculative cacheable loads, load replay, speculative predictor/TLB access.
Prohibited: visible stores before commit, wrong-path MMIO, speculative device
reads with side effects, CSR changes before commit, irreversible cache
maintenance before commit. PMA/translation must classify an access as normal
cacheable memory before aggressive speculation.

**OoO first-configuration search envelope** (starting points for synthesis
exploration, not product promises): decode/rename/commit width 2–3; ROB 48–64;
integer IQ 16–24; load queue 12–16; store queue 8–12; branch checkpoints 4–8;
2 integer ALUs; 1 branch unit; 1 LSU pipeline.

### 2.5 Agent ownership

Shared schemas have a single owner; others consume tagged versions and propose
changes via RFC PR. A0 architecture steward (contracts, `CoreConfig`, merge
order) · A1 truth/provenance · A2 HWIR · A3 hardware DI/AOP · A4 VHDL backend ·
A5 ISA/profile · A6 frontend · A7 in-order backend · A8 OoO backend · A9
LSU/cache · A10 privilege/MMU · A11 interrupt/debug · A12 FP/vector · A13
SoC/topology · A14 verification · A15 PPA/release.

**No agent edits generated VHDL directly.** Generated artifacts may be committed
as releases and goldens; source changes originate in `.spl`, profile, or
compiler files.

### 2.6 Verification — sspec-first, outside-in

```
03_system failing spec → 02_integration failing contract spec → 01_unit failing
logic spec → implementation → differential/formal evidence → synthesis/PPA evidence
```

Stack: sspec unit / integration / system · Sail differential on every retired
instruction · ACT4 (certification tests only — must be combined with
differential, random, and formal) · riscv-dv random (RV32/RV64 IMAFDC,
privilege, traps, MMU, debug; does not claim V generation) · RVFI/riscv-formal
(publicly focused on RV32I/RV64I, so extended-profile and OoO properties need
project-specific assertions) · FPGA soak · synthesis.

**Non-vacuity gates.** A system test must fail when: zero instructions retire;
the PC never changes; a required load/store or trap witness is absent; an
expected branch never resolves; a UART string came from the harness rather than
the DUT; or a timeout was read as success. *This is the same class of defect as
the JTAG-console truncation fixed in §1.3 — a capped prefix that read as a
complete log.*

**Mandatory mutants.** Each major gate must be proven to turn red under a
deliberate mutation: disable branch recovery; corrupt one C immediate bit; allow
one wrong-path store; skip one dirty writeback; ignore one interrupt; remove one
TLB invalidation; corrupt one RVV mask rule.

**Core formal properties.** x0 always zero · monotonic retirement · no double
retire · no committed instruction lost · no younger side effect survives a
redirect · stores/MMIO visible only after commit authorization · precise
exceptions and interrupts · committed rename map equals architectural state ·
free-list entries neither duplicated nor leaked · LSQ ordering satisfies fences,
aq/rl, AMO, LR/SC · dirty eviction writes the latest committed line · FENCE.I
prevents stale instruction execution · translation invalidation removes stale
TLB use · PMP/PMA applied before side effects · vector restart from vstart
equals uninterrupted execution.

### 2.7 PPA policy

Separate compile-time products, not one maximal runtime-configurable core:
`rv32_tiny`, `rv32_fast`, `rv64_inorder`, `rv64_ooo`, `rv64_ooo_vector`,
`rv64_ooo_vector2`. Unused units, ports, CSRs, queues, and debug structures are
removed during specialization and DCE.

The "single large clocked process containing the CPU" style must **not** carry
into gen2 — separate typed module and process boundaries improve synthesis
visibility, agent ownership, formal decomposition, and timing closure.

Suggested CI regression policy (project policy, not an architectural standard):
reject unexplained regressions beyond ~2–3% area, ~2–3% Fmax, or ~3–5%
benchmark performance against the matching profile baseline.

**No PPA parity claim against SiFive** without the same process node, SRAM
libraries, constraints, synthesis/PD flow, cache sizes, and enabled feature set.

---

## Immediate sequence

1. Freeze and rename V1; preserve goldens and board evidence.
2. Land machine-readable capability manifests.
3. Land **red** system specs for the verified holes: C.EBREAK, compressed
   all-zero illegal, ECALL, EBREAK, CSR writes, AMO, illegal opcodes, RV32
   halfword access, RV64C, interrupts, and the payload-address special cases.
4. Create `--hardware-strict --backend=vhdl`; certified builds never fall back.
5. HWIR v1.
6. Hardware DI elaboration; prove three configs generate different module graphs
   from one top-level source.
7. Migrate a tiny shared RV32/RV64 slice (ADD, branch, load, store, trap)
   through HWIR to VHDL.
8. Declarative ISA database; strict RV32C/RV64C legality.
9. Complete the one-/two-wide in-order core.
10. Close RVA22S64 scalar including Sv39 and Linux/OpenSBI.
11. OoO backend behind the existing contract, three-wide, frontend unchanged.
12. RVV as a decoupled subsystem; optimize after correctness closure.
13. Debug, ECC/RAS, optional AIA, coherence, security, PPA closure.

The first PR is **truth reset plus failing specs** — not a branch predictor.
