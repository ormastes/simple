<!-- codex-research -->
# Simple Compiler Performance and Memory Efficiency NFRs

## Selection

Selected by the user on 2026-08-22: **NFR Option 1 — Balanced Production Budgets**.

## Non-functional requirements

- **NFR-001 — Correctness.** Semantic differential failures are zero. Every active transform passes its positive sentinel, negative legality cases, idempotence, IR verifier, and applicable adversarial matrix.
- **NFR-002 — Fail-closed uncertainty.** Missing facts, unsupported constructs, cancellation, solver timeout, budget exhaustion, stale summaries, and unknown external behavior produce `Unknown`/`AnalysisIncomplete(reason)` and never imply safe, pure, non-escaping, non-aliasing, bounded, or constant-time behavior.
- **NFR-003 — Tier-0 cost.** After shared frontend reuse, always-on typed performance facts add median <=3% and p95 <=5% wall time on the fixed compiler/lint corpus relative to the same pinned native pure-Simple binary.
- **NFR-004 — Tier-1 cost.** Shared MIR facts and default optimized-build remarks add median <=5% and p95 <=8% release-compile wall time on the fixed compiler corpus.
- **NFR-005 — Memory.** Peak RSS regression is <=5% on fixed compiler/lint fixtures. Every long-lived cache has byte/node bounds, revision ownership, invalidation, and no unbounded retention across revisions.
- **NFR-006 — Frontend reuse.** One parse/typed-artifact owner exists per module revision. Warm lint/LSP/tool requests perform zero recursive full-tree scans and zero compiler subprocesses.
- **NFR-007 — Analysis construction.** CFG/predecessors/RPO are built at most once per function revision; downstream facts expose cache hits, rebuild reasons, node/edge counts, budget exhaustion, and elapsed time.
- **NFR-008 — Determinism.** Diagnostics, remarks, summaries, effective pipelines, and machine records are stably ordered and deterministic for identical source, target, configuration, standard-library cost-model version, and imported summary hashes.
- **NFR-009 — Diagnostic compatibility.** Existing lint text/JSON exit behavior remains compatible unless a selected requirement explicitly version-bumps it. Machine formats are versioned and JSONL stdout remains pure.
- **NFR-010 — Bounded deep analysis.** Deep/CI analyses declare maximum function/MIR size, candidate count, SCC size, expression depth/degree/variables, solver time, cancellation, and cache policy. Exceeding a bound is explicit incomplete evidence.
- **NFR-011 — Measurement provenance.** Every baseline/result records command, source commit, binary path/hash/stage/provenance, target, fixture hash/size, warmup/repetition policy, elapsed distribution, peak RSS, relevant counters, and fallback state.
- **NFR-012 — Profile overhead.** `.sprof-v2` records are optional, sampled or thresholded for production, and disabled paths do not allocate or perform I/O in hot request/loop handlers.
- **NFR-013 — Startup and hot requests.** MCP/LSP/tool-server startup and representative warm requests preserve cached artifacts, avoid repeated full-tree scans/reads/subprocesses, and meet recorded startup, request-latency, and max-RSS baselines before affected packaging/deployment is accepted.
- **NFR-014 — Portability.** Core contracts are target-independent; target profitability/layout data is injected through existing backend/HAL owners. No per-OS compiler/lint application forks are introduced.
- **NFR-015 — Verification convergence.** Each acceptance criterion is verified at most once unchanged per session, with at most three fix/verify cycles for one failing feature slice and no repeated identical failed command.

## Measurement policy

The percentage targets are design budgets until baselined on a pinned admitted native pure-Simple binary and fixed fixtures. Historical contended absolute lint times are diagnostic evidence, not release SLAs. A missing capable native host leaves its profile/hardware row explicit and incomplete; it never becomes PASS through static inspection or emulation.
