# VHDL Support Research

**Date**: 2026-02-11  
**Status**: Research summary

## Goal
Identify standards, toolchains, and semantic gaps to add a VHDL code-generation backend for the Simple compiler while keeping compile-time verification strong (loop bounds, width checks, CDC safety).

## Standards Landscape
- Current stable standard is **IEEE Std 1076-2019** (VHDL-2019). Active PAR **P1076** continues maintenance and potential updates beyond 2019.
- Key deltas vs Verilog: delta-cycle scheduling, resolved/unresolved signal types, guarded signals, shared variables/protected types, and richer package/generic mechanisms.
- Synthesis subsets vary: most vendor and open-source flows support 2008 and large parts of 2019; textio/protected types are simulation-only in many tools.

## Tooling Snapshot (open source focus)
- **GHDL**: mature VHDL front end with simulation backends (mcode, LLVM). Provides `--synth` for structural netlists and a **ghdl-yosys-plugin** to feed Yosys for synthesis.
- **Yosys + ghdl-yosys-plugin**: enables open-source synth for VHDL-2008/2019 into RTLIL, then technology mapping (nextpnr etc.).
- **GHDL LLVM backend**: LLVM-enabled builds accelerate simulation and enable mixed-language elaboration; available in recent packages.
- Other options: vendor flows (Vivado, Quartus, Libero) remain dominant for timing-closed FPGA targets; for ASIC, commercial VHDL support exists but Verilog/SV are still primary.

### GHDL Backend Comparison (mcode vs LLVM vs GCC)
| Aspect | mcode | LLVM | GCC |
| --- | --- | --- | --- |
| Userbase / default | Simplest to build; often default when multiple backends installed (Debian prefers mcode→gcc→llvm). | Common in packaged builds (e.g., `ghdl-llvm`); chosen for co-sim/perf. | Heavier toolchain dependency; usually package-installed. |
| Compile / elaborate speed | Fastest analysis/elab per GHDL docs (“rule of thumb” on x86/amd64). | Slightly slower than mcode; user reports often faster than GCC. | Slower than mcode; heavier compile pipeline. |
| Run-time sim performance | Lower performance; trade for fast compiles. | Generally fastest; public benches show 3–40% wins vs GCC. | Slower than LLVM in reported benches. |
| Outputs | In-memory execution; typically no standalone binary. | Produces executables; `-r` optional. | Produces executables like LLVM. |
| Extras | Minimal; good for quick iterations. | Balanced feature/perf; good mixed-lang story. | `gcov` coverage support is a unique plus. |
| License | GPLv2+ (same for all backends). | GPLv2+. | GPLv2+. |

### Practical Selection Guide
- Fast compile / short runs / small projects: prefer **mcode** (lowest compile latency).
- Long simulations or runtime-bound workloads: prefer **LLVM** (best runtime perf; often faster compile than GCC).
- Coverage via `gcov` required: choose **GCC** backend.

### LLVM-Based VHDL Simulators: GHDL vs NVC
| Aspect | GHDL (LLVM backend) | NVC (LLVM) |
| --- | --- | --- |
| Userbase (GitHub) | ~2.7k stars / 403 forks | ~773 stars / 99 forks |
| Performance focus | Backend choice lets you trade compile vs runtime; LLVM mode targets faster runtime. | Emphasizes simulation speed with native code via LLVM. |
| License | GPLv2+ | GPLv3+ |
| Recent release (as of 2026-02-11) | Nightlies and distro packages common; versions vary by distro. | 1.19.1 released 2026-02-07. |

## Interop Constraints vs Simple IR
- **Processes & delta cycles**: Simple MIR currently assumes edge-triggered semantics; VHDL requires careful separation of combinational processes (sensitivity lists) and clocked processes to avoid unintended latches.
- **Resolved types**: `std_logic`/`std_logic_vector` require resolution functions; Simple types map more naturally to unresolved `bit`/`bit_vector`. Need policy for choosing resolved vs unresolved per port and for multi-driver nets.
- **Generics**: map from Simple compile-time constants; must surface as entity generics for integration with existing VHDL projects.
- **Packages/libraries**: emitter should place shared type aliases and records in a package to avoid duplication across generated entities.
- **Assertions**: VHDL `assert ... severity error;` can carry the compile-time checks into simulation. For synthesis, wrap with translate_off/on or vendor-supported synthesis assertions.

## Risks / Unknowns
- Coverage of VHDL-2019 features in open-source synth is partial; ghdl-yosys lacks some protected types/textio paths.
- Name mangling and hierarchy preservation must align with both VHDL and Verilog backends to keep mixed-language projects debuggable.
- CDC/clocking semantics differ; need explicit annotation of clock/reset domains to prevent accidental latch inference in combinational processes.

## Suggested Scope for First Cut
- Target **synthesizable VHDL-2008** subset with selective VHDL-2019 features that map cleanly (records, generics, numeric_std) to reduce toolchain risk.
- Emit unresolved signals by default; opt-in resolved `std_logic` when multiple drivers or tri-states are present.
- Require static loop bounds; reject unbounded `while` at elaboration. Auto-FSM conversion for bounded loops can follow the Verilog backend policy.

## Validation Strategy
- Golden-file diffs: Simple sources → VHDL emit → compare against checked-in `.vhd` outputs.
- Round-trip synthesis sanity: run `ghdl -a -e` for analysis/elaboration and `ghdl --synth` or `yosys -m ghdl` for a small smoke-test matrix (CI optional to keep runtime modest).
- Simulation parity: co-simulate emitted VHDL with existing Verilog backend for small modules via mixed-language (GHDL + Verilator) to detect semantic drift.
