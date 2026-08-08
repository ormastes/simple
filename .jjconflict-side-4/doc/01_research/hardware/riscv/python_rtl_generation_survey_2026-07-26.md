# Python-Embedded RTL Generation Frameworks — Survey for a Simple-Language VHDL eDSL

Date: 2026-07-26. Sources: web search (amaranth-lang.org, pyrtl.readthedocs.io,
SpinalHDL docs/DeepWiki, VexRiscv repo, AMD UG901) cross-checked against model
knowledge. Purpose: inform the design of an RTL-generation eDSL in Simple that
emits VHDL for a 32/64-bit parameterized RISC-V core (KV260 / Vivado target).

## TLDR (≤30 lines)

- **All successful eDSLs are construction APIs, not host-AST translators.** Amaranth,
  Migen, PyRTL, Chisel, SpinalHDL run host code at *elaboration time* to build an
  explicit netlist/IR; only MyHDL translates host ASTs, and that is its weakest,
  most restrictive part. Simple should build an IR, never parse `.spl` bodies.
- **Two-phase model**: host values (Int, Bool, loops, if) are *generator-time*;
  `Signal`/`Value` objects are *circuit-time*. Width parameterization (XLEN=32/64)
  is just an ordinary constructor argument — free with the construction approach.
- **The IR that works**: `Signal(width, signed, reset, name)` + expression DAG
  (Op/Slice/Cat/Mux/Const) + statement trees (assign, switch) split into **comb**
  vs **per-clock-domain sync** lists, + `Instance` for black boxes, + `Memory` as a
  first-class node (never an array of signals) so Vivado infers BRAM.
- **Synthesizability is guaranteed by construction**: no latches possible because
  every comb signal has a default (its reset value, Amaranth-style); sync signals
  become one canonical clocked process per domain; resets are a domain property
  (sync default, async optional).
- **VHDL emission**: VHDL-2008 (fall back to '93-compatible subset where cheap),
  `numeric_std` `unsigned/signed`, one entity+architecture per module, `generic`
  only for pass-through knobs — widths are usually **baked at elaboration** (like
  SpinalHDL/Chisel), which sidesteps generic-propagation pain entirely.
- **AOP/debug weaving**: copy VexRiscv — build the core as plugins over a named
  pipeline/service registry; a `DebugPlugin` adds JTAG injection without touching
  other plugins. Amaranth-style hierarchy transforms are the fallback.

```mermaid
flowchart LR
  A[Simple eDSL modules\n.spl elaborate()] --> B[Netlist IR\nSignal/Expr DAG + comb/sync stmts\nMemory, Instance, Domains]
  B --> C[Passes\nlower switch->mux, const fold,\ndead-signal elim, latch check,\nname/uniquify, width check]
  C --> D[VHDL-2008 emit\nentity+arch, numeric_std,\n1 process/domain, BRAM templates]
  D --> E[Vivado / GHDL]
```

---

## 1. Amaranth (formerly nMigen) — the primary model to copy

Amaranth is the most carefully engineered of the Python eDSLs and the closest
analog to what Simple should build.

### 1.1 Core IR / abstractions
- **`Value`** — abstract expression node. Subclasses: `Const`, `Signal`,
  `Operator` (result of overloaded ops), `Slice`, `Part` (dynamic slice), `Cat`,
  `Repl`/`.replicate()`, `Mux`, `ArrayProxy` (indexable signal arrays). Every
  `Value` has a **`Shape`** = `(width, signed)`; `unsigned(32)`, `signed(8)`,
  and `ShapeCastable` for user enum/struct/fixed-point layers (`amaranth.lib.data`
  gives C-like struct/union views over a flat signal — worth copying).
- **`Signal(shape, init=..., name=...)`** — the only stateful leaf. Its `init`
  (formerly `reset=`) value doubles as (a) power-on/reset value in sync context
  and (b) **default value in comb context** — this single rule eliminates latch
  inference by construction.
- **`Elaboratable`** — a module class with `def elaborate(self, platform) -> Module`.
  Constructor takes plain Python parameters (width, depth, feature flags) — this is
  the entire parameterization mechanism. `Module()` (`m`) collects statements:
  - `m.d.comb += [sig.eq(expr), ...]` — combinational domain
  - `m.d.sync += ...` — default clock domain; `m.d.<name>` for any named domain
  - control flow via context managers: `with m.If(cond):`, `m.Elif`, `m.Else`,
    `with m.Switch(sel): with m.Case(v):`, `with m.FSM(): with m.State("A"):`
    (FSM is pure sugar lowering to a Switch over an auto-created state signal).
- **Hierarchy**: `m.submodules.name = child` (child elaborated recursively into a
  `Fragment` tree). **`Instance("vendor_prim", p_PARAM=..., i_in=..., o_out=...)`**
  for black-box/vendor primitives.
- **Memories**: `amaranth.lib.memory.Memory(shape, depth, init)` with
  `read_port(domain=..., transparent_for=...)` and `write_port(granularity=...)`
  (granularity = byte-enable lanes). Memory is an IR primitive lowered to
  `$mem_v2` cells in RTLIL / inference templates in Verilog — never unrolled.
- **Clock domains / resets**: `ClockDomain(name, reset_less=False, async_reset=False)`
  carries `clk` and `rst` signals. Every sync statement belongs to exactly one
  domain. `ResetInserter({"sync": rst2})(elab)`, `EnableInserter(...)(elab)`, and
  `DomainRenamer({"sync": "pix"})(elab)` are **wrapper transforms applied from
  outside**, without editing the wrapped design — the built-in "weaving" facility.
  `ResetSignal()`/`ClockSignal("dom")` give in-design access. Amaranth inserts
  reset synchronizers for async-reset domains via `platform`.

### 1.2 Host-language feature usage
- **Operator overloading**: `+ - * // % & | ^ ~ << >> == != < <= > >=` build
  `Operator` nodes. Width rules are value-preserving (add yields max+1 bits, mul
  yields sum of widths) then truncated on assignment to the target's width.
  Python `and/or/not` and `if sig:` are **rejected** (`__bool__` raises) — a key
  safety choice; Simple should likewise make circuit values non-truthy.
- **Context managers** give `If/Elif/Else/Switch/FSM` blocks; Python `if/for/while`
  remain elaboration-time (loop unrolling, conditional structure generation).
- **Elaboration vs run time**: everything in `elaborate()` is generator-time;
  only `Signal` values exist at circuit run time. A 32/64-bit core is
  `class Cpu(Elaboratable): def __init__(self, xlen: int): self.xlen = xlen` and
  every `Signal(xlen)` inside — no template/generic machinery needed.
- Metaprogramming is ordinary Python: dataclass-like config records,
  `amaranth.lib.wiring` `Signature`/`Component` for typed, directioned interfaces
  with `connect()` (flow-checked port bundles — strongly recommended to copy).

### 1.3 Backend pipeline
`Elaboratable` → recursive `elaborate()` → **`Fragment` tree** (per-module: list
of statements per domain, driven-signal sets, subfragments, memories, instances)
→ `Fragment.prepare()` (domain propagation/creation, missing-domain errors,
driver-conflict detection: exactly one driver per bit, comb XOR one sync domain)
→ **netlist IR** (since 0.5, an explicit flattened netlist with cells) → backends:
- `amaranth.back.rtlil` — emit Yosys RTLIL text (primary path; Yosys does real
  synthesis/opt).
- `amaranth.back.verilog` — runs Yosys (bundled as pure-Python `yowasp`) with
  `proc; memory_collect; write_verilog` — i.e. **Amaranth outsources pretty
  Verilog to Yosys**; its own passes are mostly legality + lowering, not opt.
- **No VHDL backend exists** (long-standing issue; GHDL plugin goes the other
  direction, VHDL→RTLIL). This is a gap Simple's eDSL would fill.
- Optimization: constant folding at `Operator` construction (const operands fold
  eagerly), switch→mux lowering (`LHSGroupAnalyzer` splits statements per driven
  group), everything else delegated to Yosys (`opt_clean` dead-wire removal etc.).

### 1.4 Synthesizability guarantees
- No latches: comb signals default to their `init` when not assigned.
- No multiple drivers: hard elaboration error.
- No comb loops at language level (still possible via feedback; Yosys flags).
- Sync = exactly one flop style per domain; async reset only via domain flag, so
  emitted always/process templates are canonical and tool-friendly.
- Memories emitted as inference-template code or `$mem` cells → BRAM maps well.

### 1.5 Instrumentation / AOP
- `ResetInserter` / `EnableInserter` / `DomainRenamer` wrap a finished design.
- Fragment tree is walkable post-elaboration: you can add submodules/statements
  to any fragment before `prepare()` — a supported (if low-level) way to weave
  taps. No named join-point system; hierarchy paths + signal names are the hooks.

## 2. Migen (the ancestor)
- IR: `Signal(bits_sign)`, expression nodes, statements `sig.eq(expr)`,
  `If(cond, ...).Else(...)`, `Case`. A `Module` has `self.comb += ...` and
  `self.sync += ...` / `self.sync.domainname += ...`; `self.submodules += ...`;
  `self.specials += Instance(...)/Memory(...)`. "Specials" = things that bypass
  the FHDL statement language (memories, instances, tristates).
- FHDL is a plain Python object tree; `migen.fhdl.verilog.convert()` walks it and
  prints Verilog directly (no external tool). Only trivial lowering (no real opt
  passes). Latch avoidance: comb signals get `initial`-style defaults in the
  generated always @(*) block (each comb block starts by assigning defaults).
- Clock domains: `ClockDomain` objects; `ClockDomainsRenamer` transform mirrors
  Amaranth's `DomainRenamer`.
- Weakness vs Amaranth: no shapes/signedness discipline, weaker error checking,
  Verilog printer must handle everything. Amaranth is Migen with a real IR and
  a legality layer; study Migen only as the minimal-viable data model.
- Ecosystem note: LiteX (SoC builder, CSR bus auto-generation, cross-domain FIFO
  library) shows the payoff of the approach — SoC integration is elaboration-time
  Python composing modules.

## 3. MyHDL — the AST-translation cautionary tale
- Model: hardware = Python **generator functions** decorated `@always_comb`,
  `@always_seq(clk.posedge, reset=...)`, `@always(...)`; signals are `Signal(intbv(0)[8:])`
  (intbv = constrained integer with bit-slicing). Simulation runs the actual
  Python generators (event-driven, `yield` = wait).
- **Conversion** (`toVerilog`/**`toVHDL`**): grabs the function **source via
  `inspect`, re-parses to a Python AST**, infers types/widths from intbv bounds,
  and translates a *convertible subset* to HDL. Anything outside the subset
  (arbitrary method calls, dynamic structures) is a conversion error found late.
- VHDL output details (relevant to us): emits VHDL-93/2002-compatible code using
  `numeric_std` plus a small support package `pack_myhdl`; `intbv` → `unsigned`/
  `signed`; `@always_seq` → canonical clocked process with sync or async reset
  chosen by the `ResetSignal(active=..., isasync=...)` object — a nice API: reset
  polarity/asynchronicity is a property of the reset signal, and reset assignment
  of every registered signal is **auto-generated** from initial values (mirrors
  Amaranth's init rule).
- Hierarchy: function calls returning instance lists; conversion flattens naming
  via call-tree analysis. Memories: list-of-Signal → inferred RAM if the access
  pattern fits; brittle in practice.
- Lesson for Simple: **do not** translate Simple ASTs. Late, subset-based errors
  and simulation/synthesis semantic gaps are the recurring MyHDL complaints. But
  DO steal: reset-signal-as-object, auto reset assignment, numeric_std mapping.

## 4. PyRTL — the clean-netlist datapoint
- IR: a flat global `Block` of `LogicNet`s: `(op, op_param, args, dests)` with
  ops in `w~&|^n+-*<>=xcsr m@` (wire, not, and, or, xor, nand, add, ..., mux,
  concat, select, register, memread, memwrite). `WireVector(bitwidth)`,
  `Register`, `Input/Output/Const`, `MemBlock`/`RomBlock`.
- Everything is structural; conditional assignment via
  `with pyrtl.conditional_assignment: with cond: r.next |= v` (context managers
  again). **Single implicit clock**, no clock domains, register reset =
  reset_value parameter → deliberately narrow but trivially correct.
- **Passes (the best-documented optimization set of the group)**:
  `optimize()` = constant propagation + common-subexpression elimination +
  removal of unlistened (dead) nets; `synthesize()` lowers to 1-bit gates;
  analysis: `area_estimation`, `TimingAnalysis` (critical path), `yosys_area_delay`.
  Output: `output_to_verilog` (plus firrtl). Demonstrates that on a pure netlist
  IR, const-fold/CSE/DCE are each ~100 lines — Simple should implement exactly
  these three plus the latch/driver checks, and stop.

## 5. Chisel / FIRRTL (Scala) — brief
- `Module` classes with `IO(new Bundle{...})`; `UInt/SInt/Bool` values; `:=`
  connect; `when/.elsewhen/.otherwise`; `Reg`, `RegInit`, `Mem/SyncReadMem`;
  implicit clock+reset per module scope (multi-clock via `withClock(...)`).
- Parameterization = Scala constructor args + type parameters + `Config`/`Parameters`
  objects (rocket-chip); functional generators (`Seq.tabulate`, folds) everywhere.
- **Key architectural lesson: FIRRTL**, a serialized, spec'd IR with a compiler
  of ordered passes (high→mid→low forms): infer widths, expand whens (⇒ no
  latches: every when is completed with defaults), lower bundles to ground
  types, const prop, DCE, then emit Verilog (today via CIRCT/MLIR `firtool`).
  Passes are *transform* classes users can insert — the sanctioned AOP hook
  (e.g., coverage/tap insertion transforms, "Wiring" transform to punch signals
  through hierarchy; SiFive used FIRRTL transforms to weave DFT/debug logic).
- Cost: heavy infrastructure. For Simple, a mini-FIRRTL (one in-memory IR, fixed
  pass list, user-insertable passes) captures 90 % of the value.

## 6. SpinalHDL (Scala) — brief, but the best VHDL emitter + best AOP story
- Same construction model (Component/Area, Bool/UInt/SInt/Bits, `:=`,
  `when/otherwise/switch`, `Reg(...) init(...)`). **ClockDomain** is an explicit
  object bundling clk+reset+enable with a config: reset kind (ASYNC/SYNC/BOOT),
  polarity, clock-enable — applied via `ClockingArea(cd) { ... }`. This is the
  most complete clock/reset model of any framework; copy it.
- Compilation: elaboration builds a graph, then a **PhaseContext runs ~40 ordered
  phases** (type/width inference & checks, combinational-loop detection **at
  elaboration** — a genuine graph check, latch detection, cross-clock-domain
  violation detection, dead-code removal, naming), then a backend emitter.
- **VHDL backend is first-class**: emits VHDL-93-compatible code, `numeric_std`,
  one entity/arch per Component, canonical processes; memories emitted as
  inference-friendly templates or optionally as black-box vendor macros. Its CDC
  and comb-loop checks are marketing-level features ("checks that go beyond what
  RTL can do"). Generated code bakes parameters (no generics) — Scala is the
  generic system.
- **AOP: VexRiscv** builds the CPU as a `Pipeline` of `Stage`s with a typed
  key-value **Stageable** system (insert a value in stage X, read it in stage Y;
  pipeline registers auto-inserted) plus a **service registry** (plugins ask for
  services other plugins expose). `DebugPlugin` implements the whole on-chip
  debug (halt, single-step, hardware breakpoints, bus access) by requesting an
  *instruction-injection port* from the fetch service — **JTAG debug is woven in
  by adding one plugin to the config list, zero edits to other plugins.** Its
  successor VexiiRiscv generalizes this (Plugin/Fiber elaboration with retains/
  locks). This is the model for our "weave JTAG into the core" requirement.
- Also has `Component.rework { }` / composable Areas to patch a component after
  definition, and automatic pruning of unused signals.

## 7. Clash (Haskell) — brief
- Not an eDSL: a **compiler for a subset of Haskell itself** (GHC Core →
  netlist). Circuits are functions on `Signal dom a`; registers = `register`
  primitive; `dom` is a *type-level* clock domain carrying period/edge/reset
  kind (synchronous/asynchronous) — domain correctness is type-checked.
- Parameterization via type-level naturals (`Unsigned n`, `Vec n a`): an XLEN
  template is `forall n. KnownNat n => ...` — the strongest static story, at the
  cost of needing a dependent-ish type system.
- Emits VHDL-93, Verilog, SystemVerilog directly; memories via `blockRam`
  primitives that expand to vendor-inference templates; `ANN`/`Synthesize`
  annotations control entity names/ports. Lesson: type-level widths are elegant
  but not required — constructor-arg widths (Chisel/Amaranth) deliver the same
  XLEN=32/64 outcome with far less type machinery.

---

## 8. Synthesizability & Vivado-specific pitfalls (target: KV260, VHDL)

1. **Latch inference** — only possible from incomplete comb processes. Amaranth
   rule (comb default = init value) or Chisel rule (when-expansion completes all
   branches) makes it impossible. Emit comb processes that assign defaults first.
2. **Resets** — Zynq UltraScale+ fabric prefers **synchronous, active-high**
   resets (better LUT packing, BRAM/DSP output registers have sync rst only).
   Make sync-reset the default domain config; async reset a per-domain option
   emitted as the canonical `if rst then ... elsif rising_edge(clk)` form. Never
   reset BRAM contents (only output registers) or inference breaks.
3. **Vivado BRAM inference (UG901 idioms, VHDL)**:
   - RAM = `signal ram : ram_type;` where `type ram_type is array (0 to DEPTH-1)
     of std_logic_vector(...)`; write and (registered) read inside the same
     clocked process; **read-first**: `q <= ram(addr); if we then ram(addr) <= d;`
     — ordering/mode must be emitted deliberately (read_first/write_first/
     no_change map to BRAM primitive modes).
   - Byte enables: VHDL-2008 shared-variable-free loop-over-lanes template, or
     per-lane generate; UG901 has both WRITE_FIRST and READ_FIRST byte-enable
     templates — emit exactly those shapes.
   - `attribute ram_style of ram : signal is "block"|"distributed"|"ultra";` as
     an escape hatch; also `RAM_DECOMP` for depth-wise decomposition.
   - Asynchronous read ⇒ distributed RAM (LUTRAM) only; dual-clock true-dual-port
     needs the specific UG901 two-process template. Add an output register stage
     option to hit BRAM's optional output register (frequency!).
   - Known project landmine (KV260 campaign 2026-07-26): Vivado pads non-pow2
     BRAM depth to pow2 — size arrays pow2 or accept the padding.
4. **DSP inference** — write `p <= a * b + c` patterns with registers before/
   after (pipeline regs get pulled into DSP48E2); `attribute use_dsp of ... :
   signal is "yes"|"no"`. Signed multiply of `signed(a)*signed(b)` with full
   product width; then slice. Avoid resets on DSP pipeline regs (or use sync rst).
5. **General**: no signal driven from two processes (check in IR); no shared
   variables (except the legacy TDP-RAM template); every FSM as one sync process
   + optional comb next-state process; initial values on signals are honored by
   Vivado for FPGA (power-on state) — can emit `:= init` and keep reset optional.

## 9. VHDL emission specifics for the Simple eDSL

- **Dialect**: target **VHDL-2008** (Vivado, GHDL, Questa all fine in 2026) but
  keep the emitted subset '93-friendly where free. 2008 features worth using:
  `unsigned`/`signed` condition sugar avoided; but use: `process(all)` — NO,
  prefer explicit sensitivity or fully-registered style; genuinely useful 2008
  items: fixed `to_string` for asserts in testbenches, reading output ports
  (buffered internally instead is safer), enhanced generics only if needed.
  Safest: emit '93-compatible bodies, declare `--! vhdl-2008 ok`.
- **Types**: ports `std_logic` / `std_logic_vector`; internal arithmetic in
  `unsigned/signed` from `ieee.numeric_std`; convert at boundaries only
  (`unsigned(slv)`, `std_logic_vector(u)`). Never `std_logic_arith`.
- **Module mapping**: one IR module → `entity` (ports) + `architecture rtl`
  (decls + one process per sync domain + comb assignments/processes + instance
  `port map`s). Deterministic, stable signal naming (hierarchy-prefixed) — vital
  for diffability and for ILA/JTAG tap addressing.
- **Generics vs baked parameters**: two viable modes —
  (a) *bake* (SpinalHDL/Chisel): elaborate twice for XLEN=32 and 64, emit
  `rv32_core.vhd` / `rv64_core.vhd`. Simplest, recommended default; the eDSL is
  the generic system.
  (b) *pass-through generics*: for values that stay symbolic (depths, init
  files), emit `generic (XLEN : positive := 64)` and `port (rd : out
  std_logic_vector(XLEN-1 downto 0))`, instantiations use `generic map (XLEN =>
  32)`. Support only where every use of the parameter is affine (widths/ranges);
  anything conditional on the parameter (RV64-only instructions!) forces baking
  anyway. RISC-V XLEN changes the *instruction set*, not just widths ⇒ bake.
- **Processes**: sync domain `dom` →
  `process(clk) begin if rising_edge(clk) then if rst='1' then <resets> else
  <body> end if; end if; end process;` (async variant reorders). Comb → either
  concurrent assignments (preferred when statements lower to muxes) or one
  process with defaults-first.

## 10. AOP / instrumentation — synthesis across frameworks

| Mechanism | Framework | Granularity |
|---|---|---|
| Wrapper transforms (ResetInserter/EnableInserter/DomainRenamer) | Amaranth/Migen | whole submodule, from outside |
| Post-elaboration fragment/graph editing | Amaranth, SpinalHDL `rework` | any signal, unsanctioned-ish |
| IR-level pass insertion (Wiring/tap transforms) | FIRRTL/Chisel | any named signal, sanctioned |
| **Plugin + service registry + pipeline Stageables** | SpinalHDL/VexRiscv | semantic join points; the gold standard |
| BoringUtils (`bore` a signal up through hierarchy) | Chisel | single-signal punch-through |

For the "weave JTAG debug into the core without editing it" requirement (repo
already has `riscv32_riscv64_unification_realrtl_aop_jtag_2026-07-21.md`):
1. Structure the core generator as **plugins over a pipeline with named
   Stageable keys and services** (fetch-injection service, CSR service,
   trap service). DebugPlugin = halt-request + instruction injection via fetch
   service + DM registers — the VexRiscv recipe, proven with OpenOCD.
2. Additionally provide a generic **IR tap pass**: given hierarchical signal
   names, auto-punch ports up the hierarchy (BoringUtils-style) to a JTAG/ILA
   capture block — for ad-hoc bring-up probes without redesign.

## 11. Recommended design for the Simple RTL eDSL (concrete)

1. **Construction eDSL, two-stage**: Simple code runs at elaboration; circuit
   values are `Sig` objects. No Simple-AST translation.
2. **IR**: `Module{name, ports, signals, comb: [Stmt], sync: Dict<Domain,[Stmt]>,
   mems: [Mem], insts: [Instance], subs: [Module]}`; `Expr` DAG (Const, Ref,
   Op, Slice, Cat, Repl, Mux); `Stmt` = Assign | Switch. Shapes = (width,
   signed) checked at construction; const-fold in the Op constructor.
3. **Semantics rules (checked, not documented)**: single driver per signal;
   comb defaults from `init` (no latches); each signal comb XOR one domain;
   `Sig` not usable as Simple Bool (compile/elab error).
4. **Domains**: SpinalHDL-style `ClockDomain{clk, rst, kind: Sync|Async|None,
   polarity, enable}`; default = sync active-high (KV260-friendly); transforms
   `rename_domain`, `insert_enable`, `insert_reset` as module wrappers.
5. **Memory as primitive** with mode (read_first/write_first), optional output
   register, byte-granularity; emit UG901 template shapes verbatim; `ram_style`
   attribute knob; pow2-depth lint (Vivado padding landmine).
6. **Passes (only these)**: switch→mux lowering, const fold, DCE (unlistened
   nets, PyRTL-style), uniquify/name, legality checks, then user-insertable tap
   passes. Heavy opt belongs to Vivado/Yosys, not us.
7. **VHDL-2008 emitter** per §9; golden-file tests + GHDL analyze (`ghdl -a
   --std=08`) as the CI synthesizability gate, plus periodic Vivado
   `synth_design -rtl` lint on the KV260 project.
8. **Parameterization**: constructor args; XLEN handled by baking two
   elaborations (rv32/rv64) sharing one generator — matches the existing
   rv32/rv64 unification plan; generics only for depths/init-file paths.
9. **Interfaces**: Amaranth-`wiring`-style `Signature` bundles with direction
   checking and `connect()`; define Wishbone/AXI-lite/JTAG-DTM signatures early.
10. **Core architecture**: VexRiscv-style plugin/pipeline framework so the JTAG
    DebugPlugin, CSR sets, and RV32/RV64 ALU variants are plugins — AOP by
    architecture, taps by IR pass as the escape hatch.

## Sources
- https://amaranth-lang.org/docs/amaranth/ (language guide, changes 0.4→0.5 netlist IR)
- https://github.com/amaranth-lang/amaranth ; https://deepwiki.com/amaranth-lang/amaranth
- https://pyrtl.readthedocs.io/en/latest/analysis.html (optimize/CSE/const-prop/dead-net)
- https://yosyshq.readthedocs.io/projects/yosys/en/stable/yosys_internals/formats/rtlil_rep.html
- https://deepwiki.com/SpinalHDL/SpinalHDL/3-compilation-and-code-generation (PhaseContext)
- https://spinalhdl.github.io/SpinalDoc-RTD/ (ClockDomain config, checks)
- https://github.com/SpinalHDL/VexRiscv (plugin/Stageable/DebugPlugin, nativeJtag)
- https://spinalhdl.github.io/VexiiRiscv-RTD/master/VexiiRiscv/Debug/index.html
- https://docs.amd.com/r/en-US/ug901-vivado-synthesis/ (BRAM byte-enable read/write-first VHDL templates)
- https://docs.amd.com/r/2023.1-English/ug912-vivado-properties/RAM_STYLE ; RAM_DECOMP
- https://danielmangum.com/posts/when-vivado-infer-bram/
- https://tomverbeure.github.io/2021/07/18/VexRiscv-OpenOCD-and-Traps.html
- MyHDL: http://docs.myhdl.org (conversion subset, toVHDL, ResetSignal) — from model knowledge, cross-checked shape only.
- Clash: https://clash-lang.org — model knowledge (type-level domains/KnownNat).
