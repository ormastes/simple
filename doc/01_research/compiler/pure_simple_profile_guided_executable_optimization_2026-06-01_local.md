<!-- codex-research -->
# Pure Simple Profile-Guided Executable Optimization Domain Research

Date: 2026-06-01

## Sources

- LLVM PGO build guide:
  `https://llvm.org/docs/HowToBuildWithPGO.html`
- LLVM BOLT README:
  `https://github.com/llvm/llvm-project/blob/main/bolt/README.md`
- Linux `perf_event_open(2)` manual:
  `https://man7.org/linux/man-pages/man2/perf_event_open.2.html`
- GDB breakpoint user documentation:
  `https://sourceware.org/gdb/current/onlinedocs/gdb.html/Set-Breaks.html`
- RISC-V Debug Specification debug module:
  `https://github.com/riscv/riscv-debug-spec/blob/master/debug_module.adoc`

## Findings

### PGO Is A Controlled Multi-Stage Loop

LLVM PGO practice separates instrumented build, workload execution, profile
merge, and optimized rebuild. Simple should mirror that shape:

1. build or run with profile collection enabled;
2. execute representative workloads;
3. merge counters into `.sprof`;
4. apply profile data in optimize/build stages.

Do not load profiles implicitly in unrelated commands.

### BOLT-Like Optimization Is Post-Link Layout Work

LLVM BOLT is a post-link binary optimizer driven by profile data. The requested
Simple version should not shell out to BOLT. Instead, the pure-Simple optimizer
should own a constrained layout pass over Simple executable metadata:

- function order;
- hot/cold block grouping;
- branch fallthrough preference;
- alignment hints;
- optional cold-section splitting when metadata supports it.

The first Simple implementation should target settlement/native metadata where
symbol and relocation semantics are controlled by the repo.

### Sampling And Overflow Counters Avoid Trap-Heavy Paths

Linux `perf_event_open` demonstrates a low-overhead design shape: counters can
sample events, use periods, deliver overflow notifications, and expose data
through shared buffers. Simple bare-metal cannot copy Linux perf wholesale, but
the design lesson is important: prefer sampled counters or hardware counters
over trap-on-every-hit when execution would become too slow.

### Software Breakpoints Are Precise But Expensive

GDB-style breakpoints are precise stop points, and hardware breakpoints are a
scarce separate mechanism. Software breakpoint counters patch code and trap on
execution, so they are appropriate for short profiling windows, rare edges, or
bootstrap-only call-path discovery. They are not acceptable as permanent hot
loop counters.

### Bare-Metal Debug Specs Need Explicit Ownership

RISC-V debug modules show the separation between target execution and debug
control. Simple's bare-metal plan should model breakpoint counters as an
explicit debug/profiling capsule with state transitions:
`armed -> hit -> counted -> single-step/restore -> rearm` or
`armed -> over-budget -> disarmed`.

## Design Pressure

- Use `.sprof` as the cross-mode profile record.
- Use instrumented native counters for common function/block/edge counts.
- Use software breakpoints only for sparse call-path discovery and bootstrap
  probes.
- Auto-remove breakpoints when trap overhead exceeds a configured budget.
- Build pure-Simple executable layout optimization over Simple metadata first;
  do not require external BOLT.
