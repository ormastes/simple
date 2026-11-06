<!-- codex-design -->
# Release 1.0.0 memory and MCP/LSP architecture

Status: design contract; implementation and runtime admission **OPEN**. Full authority: [selected feature requirements](../02_requirements/feature/release100_memory_mcp_lsp.md), [NFRs](../02_requirements/nfr/release100_memory_mcp_lsp.md), and their retained source plans. This document does not supersede the plans' detailed algorithms or prove deployment.

## Ownership and dependency boundaries

Memory plan §§3–9 and 15 preserve one mandatory typed ownership authority, CFG-sensitive move/short-borrow facts, cleanup elaboration and route-specific lowering validation. Interpreter paths must consume the common checked facts without redundant full target MIR. Native backends preserve and validate the facts. Optional cycle/escape analysis must not disable ownership, drop or short-borrow safety. Legacy semantics require an explicit migration boundary; an admitted strict no-GC route cannot permit a safety bypass.

Compiler stage contracts share Parse/HIR/MIR/OBJ implementations between fused, split, checkpoint and replay scheduling. A ready unit or necessary SCC owns mutable scratch; the session owns immutable published data. Publication requires frozen independent storage, complete source/semantic identity and a live producer generation. Reader leases prevent eviction; handles include owner, slot and nonwrapping generation. Runtime/provider behavior must be verified separately from compiler code generation.

MCP/LSP plan §3 separates shared source contracts/store/providers/analysis/projection/session/transactions/config-analysis/change-analysis/debug-bridge from protocol/UI adapters. A protocol handler performs translation, not private semantic parsing, duplicate caching or target ownership. Libraries remain below composition roots. Existing native parsers, DiagnosticV1, cache gateways, document owners and DebugServiceV1 are reused; app platform differences remain behind SOSIX/HAL owner interfaces.

DebugServiceV1 alone owns target sessions, execution commands, breakpoints/evaluation and mutation leases. Source views may consume read-only stop snapshots pinned to build, code generation and stop epoch. An edit is not a live replacement; replacement must use the existing debugger admission transaction. No new frontend-specific evaluator or session registry is allowed.

MDSOC may organize cross-cutting provenance, capabilities and observability at existing seams. It does not justify new kernel/driver weaving, dependency inversion violations, or independent copies of compiler semantics. Shared contracts plus thin adapters are the chosen integration pattern; physical file placement remains subject to current owner review.

## Startup and request cost review

| Path | Required behavior | Evidence still required |
|---|---|---|
| Process startup | Load lightweight contracts, bounded session/document authority and protocol registration; lazy providers | Cold-start time/RSS, loaded modules and subprocess counters for exact built binaries |
| Cached outline/raw open | Immutable source + existing syntax/position map; no compiler/test/history/environment/debugger startup | Front-door output, exact ranges, capability limitations, read/parse/process counters |
| Display toggle | Versioned session update + existing projection; no reparse/recheck or semantic-key change | Idempotence/concurrency fixtures and p95 <20 ms |
| Semantic navigation/detail | Reuse shared semantic index keyed by relevant context; request only needed facts | p95 <200 ms, bounded traversal, cancellation and incomplete boundaries |
| Cold semantic provider | Trusted configured lazy launch, bounded startup/output/restart, correct overlay and target | Per-provider identity/trust/lifecycle receipts; distinct cold latency |
| History/environment/flow | Explicit operation, fixed query identity, progress/deadline/cancellation and redaction | First-result/total time, bounds reached, no hidden passive-reader execution |

Cached outline p95 target is <100 ms. Initial focused output is approximately 2,000 model-visible tokens including structured data. Root must pin absolute startup/RSS and host-specific resource caps before admission; the input plans do not supply universal values. Full-tree scans, repeated reads and per-request shell-outs are prohibited on ordinary hot paths unless a documented maintenance/reindex operation demonstrates necessity and bounded cost.

## Cache, index and invalidation review

Source snapshots bind workspace, document URI, original/decoded content identity, overlay owner/version, language/dialect and parser generation. Semantic keys additionally include dependency/read-set generations, negative resolution, provider/compiler, target/features/ABI, grammar and expansion/aspect state. Runtime observations additionally bind debug target/build/code generation/epoch. Compact hashes accelerate lookup but cannot prove identity; private XXH3 collision resolution and strong untrusted-boundary identity remain mandatory.

Single-flight production admits one complete immutable result; cancelled waiters do not destroy work still needed by others. Failed/incomplete producers never publish success. Query cursors bind query, snapshot, provider generation and access scope. Eviction waits for actual reader quiescence; old unpinned generations retire inside explicit quotas. Failed `.rr` publication requires the established consistency recheck before reuse. Presentation preferences never invalidate syntax or semantic caches.

A file edit either creates a new immutable snapshot or explicitly invalidates old handles/cursors. Historical snapshots can remain readable under authorization but cannot silently authorize writes. Changed semantic environment invalidates affected semantic artifacts, not every syntax result. Debug resume invalidates live frame/value handles; frozen evidence retains its old epoch and cannot impersonate current state.

## Current evidence boundaries

Parallel audit findings are provisional until root reviews exact files and receipts: current release code contains ownership-flow/strict MIR and AOT gates, and newer structured LSP code-action/call-hierarchy work; these must be preserved. A `--no-borrow-check` early return is being checked for strict no-GC bypass. MCP reader empty-file handling, warning visibility and colon-delimited Windows paths are under repair. Shared source-view/session/projection coverage is incomplete. None of these observations establishes all plan requirements or real front-door parity.

The deployed binary's directory/name does not prove pure-Simple provenance. The inspected bootstrap is terminal: PID 25734 is absent and its full-CLI HIR stage failed on unresolved `exit` in an older worktree. The current release base already imports `exit`; this does not prove a rebuilt runtime. Runtime admission remains BLOCKED pending a fresh exact candidate and receipts. No active wait, duplicate bootstrap, seed substitution, static-only PASS or unverified capability promotion follows from this architecture.
