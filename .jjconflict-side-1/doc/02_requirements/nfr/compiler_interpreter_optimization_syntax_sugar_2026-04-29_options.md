# NFR Options: Compiler/Interpreter Optimization + Syntax Sugar

**Date:** 2026-04-29
**Decision required:** choose one option.

## NFR A: Startup and Tooling Focus

**Targets**

- Warm CLI startup for cached tooling commands improves by at least **25%** on a representative workspace fixture.
- Cross-session cache invalidation is deterministic and testable.
- Any new cache or startup optimization must report:
  - warm startup time,
  - cold startup time,
  - peak RSS.

**Pros**

- Matches MCP/LSP/CLI workflow pain directly.
- Easy to verify with repeatable benchmarks.
- Forces disciplined cache design.

**Cons**

- Says little about steady-state interpreter throughput.
- Can bias design toward short-lived process wins over long-running workloads.

**Effort**

- **Medium**

## NFR B: Interpreter Throughput Focus

**Targets**

- Selected hot interpreter workloads improve by at least **15%** on representative benchmarks.
- Mis-specialization fallback remains correct and measurable.
- Any adaptive optimization must expose counters or diagnostics for:
  - specialization attempts,
  - de-specializations,
  - cache hit/miss behavior.

**Pros**

- Forces real hot-path performance evidence.
- Well aligned with adaptive specialization and inline-cache work.

**Cons**

- Harder to verify than startup-only targets.
- Requires benchmark discipline and careful workload choice.

**Effort**

- **Medium-Large**

## NFR C: Balanced Tooling + Runtime

**Targets**

- Warm startup improves by at least **20%** on a representative tooling workflow.
- Selected hot interpreter workloads improve by at least **10%**.
- Peak RSS must not regress by more than **10%** unless explicitly justified.
- New syntax sugar must lower to forms with no measurable regression on covered benchmarks.

**Pros**

- Best fit for a mixed roadmap.
- Prevents ergonomics work from silently hurting runtime behavior.
- Keeps both startup and throughput visible.

**Cons**

- Requires the broadest benchmark coverage.
- Hardest option to manage if scope grows.

**Effort**

- **Large**

## NFR D: Documentation and Observability First

**Targets**

- Every approved feature request must define:
  - affected compiler/runtime stages,
  - expected latency/startup/RSS impact,
  - verification plan,
  - rollback criteria.
- No hard numeric performance target yet.

**Pros**

- Good fit if you want architecture clarity before perf commitments.
- Low immediate execution risk.

**Cons**

- Weakest pressure toward measurable improvement.
- Easy to keep researching without converging.

**Effort**

- **Small**
