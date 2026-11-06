<!-- codex-design -->
# Release 1.0.0 memory hardening and MCP/LSP requirements

Status: **OPEN; implementation and execution admission pending.** Baseline: `origin/release/1.0.0` at `e2ce7042552` on 2026-11-06.

## Selected authority and interpretation

The user selected both complete plans: [memory hardening](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) and [MCP/LSP improvement](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md). Their normative text, examples' declared limitations, cross-references, requirement tables, proof obligations, matrices, and release checklists remain authoritative. This register adds stable tracing; it does not replace or narrow those contracts. The retained input hashes are recorded in `.spipe/release100_memory_mcp_lsp/state.md`.

Source findings must be rechecked against the implementation before acceptance. A stale baseline statement in an input does not authorize undoing a later repair. Existing behavior can satisfy a requirement only with current code and route-specific execution evidence. Every row begins OPEN, including implemented-looking code without admitted evidence.

The input MCP plan §20.1 suggests executable specs under `doc/06_spec`; repository policy takes precedence: executable `.spl` specs belong under `test/`, and their generated/manual Markdown mirrors belong under `doc/06_spec`. Unsupported/unavailable hosts remain OPEN/BLOCKED rather than disappearing from scope or counting as PASS.

## Repository corrections and conflict handling

The retained Downloads inputs remain byte-for-byte historical selection evidence. Preserve the canonical [ownership recovery plan](../../03_plan/language/memory_safety/nogc_ownership_recovery_plan_2026-10-19.md) and [memory language design](../../05_design/language/misc/memory.md), including their prior user decisions and dated corrections. Do not overwrite them with an older downloaded draft.

| Conflict or correction | Treatment | Status |
|---|---|---|
| Pointer sigils in prior drafts | Preserve canonical correction: `&T` is owning unique, `*T` is reference-counted; short borrowing is a checked parameter effect, not an invented Rust-style pointer spelling. The canonical document's unresolved wording/proposals retain their explicit status. | Existing correction retained; implementation evidence OPEN |
| User-selected contract versus older inspected baseline | Selected behavior remains required; later code fixes and evidence corrections are preserved and re-audited, not reverted to match stale prose. | OPEN audit |
| Actual semantic conflict between selected input and canonical prior decision | Record exact conflicting passages and affected requirement; root resolves from prior user authority or requests the missing decision. No silent auto-selection or reinterpretation. | OPEN if discovered |
| Executable SSpec placement | Repository `test/` + `doc/06_spec/*.md` policy overrides input §20.1's placement suggestion. | Resolved documentation constraint |

Current evidence lives in [memory baseline](../../08_tracking/audit/release100_memory_mcp_lsp_2026-11-06/memory_baseline.md), [MCP/LSP baseline](../../08_tracking/audit/release100_memory_mcp_lsp_2026-11-06/mcp_lsp_baseline.md), and [runtime admission](../../08_tracking/audit/release100_memory_mcp_lsp_2026-11-06/runtime_admission.md). These audits remain evidence with stated scope, not blanket acceptance.

An initial documentation-only PR may preserve inputs, requirements and audit findings independently. Its merge satisfies documentation preservation only; it does not close implementation, runtime, proof, platform, performance or overall goal acceptance.

## Whole-plan section register

Each `REQ-*` row incorporates **all** text and subsections at the referenced section. Parent rows include tables, numbered lists, unnumbered paragraphs, companion dependencies and stated exclusions. Child rows support precise evidence assignment; satisfying a parent requires satisfying all applicable children. Source/evidence reference sections require provenance integrity, not implementation of cited third-party products.

| Requirement | Selected plan section | Acceptance owner | Status |
|---|---|---|---|
| REQ-MEM-1 | [1 Decisions and scope](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-1-1 | [1.1 Required defaults](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-1-2 | [1.2 What “recover” means](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-1-3 | [1.3 Scope of guarantees](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-1-4 | [1.4 Implementation notation](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-2 | [2 Repository evidence and corrections](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-2-1 | [2.1 Review boundary and Bug DB freshness](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-2-2 | [2.2 Findings that change the implementation plan](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-2-3 | [2.3 Corrections to historical attribution](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-2-4 | [2.4 Evidence levels](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-3 | [3 Recover no-GC unique ownership and short borrowing](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-3-1 | [3.1 Normative ownership contract](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-3-2 | [3.2 Strictly short borrowing—no range expansion](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-3-3 | [3.3 Function and method contracts](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-3-4 | [3.4 Owner state machine and control-flow handling](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-3-5 | [3.5 Containers, replacement, and failed operations](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-3-6 | [3.6 Exactly-once cleanup and foreign resources](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-3-7 | [3.7 One mandatory checker across execution routes](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-3-8 | [3.8 Compatibility and bootstrap recovery](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-4 | [4 Cyclic relationships and configurable detection](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-4-1 | [4.1 Ownership cycles are not ordinary graph cycles](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-4-2 | [4.2 Recommended representations](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-4-3 | [4.3 Cycle-check policy](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-4-4 | [4.4 No longer borrowing as a cycle workaround](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-5 | [5 Fused compiler with separable debugging phases](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-5-1 | [5.1 What “one pass by default” means](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-5-2 | [5.2 One set of stages, multiple execution policies](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-5-3 | [5.3 Declaration readiness, SCCs, and global work](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-5-4 | [5.4 Sharing at each stage](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-5-5 | [5.5 Debugging without default retention](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-6 | [6 Phase-local memory and safe publication](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-6-1 | [6.1 Lifetime map](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-6-2 | [6.2 Arena rules](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-6-3 | [6.3 Publication protocol](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-6-4 | [6.4 Bounded queues and backpressure](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-7 | [7 Build-runner immutable sharing and session lifecycle](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-7-1 | [7.1 Default session authority](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-7-2 | [7.2 Unique session owner, shared reads, short access](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-7-3 | [7.3 Physical sharing across processes](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-7-4 | [7.4 Processes versus threads](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-7-5 | [7.5 Session duration is not retention duration](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-7-6 | [7.6 Source inventory and editing integration](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-7-7 | [7.7 Single-flight and crash-safe publication](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-8 | [8 XXH3 and BLAKE3 content-identity policy](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-8-1 | [8.1 Trust policy—not “cryptographic hashing everywhere”](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-8-2 | [8.2 Collision correctness in private mode](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-8-3 | [8.3 Separate identities by semantic role](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-8-4 | [8.4 Streaming hashing and bounded validation](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-9 | [9 Runtime, process, and scheduler hardening](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-9-1 | [9.1 Hidden copies and allocator registries](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-9-2 | [9.2 Process lifetime and orphan prevention](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-9-3 | [9.3 Memory-aware scheduling](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-9-4 | [9.4 Failure outcomes and diagnostic survival](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-9-5 | [9.5 File handles, source authority, and OS/device resources](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-10 | [10 Language-level changes: required, optional, and rejected](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-10-1 | [10.1 Required beyond repairing the default owner](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-10-2 | [10.2 Optional diagnostics and optimization](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-10-3 | [10.3 Explicitly rejected approaches](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-11 | [11 Formal verification and implementation refinement](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-11-1 | [11.1 Verification strategy](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-11-2 | [11.2 Required proof obligations](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-11-3 | [11.3 Lean4 proof admission](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-11-4 | [11.4 Bridge to production code](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-11-5 | [11.5 Claims intentionally not made](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-12 | [12 Acceptance tests and protection against removal](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-12-1 | [12.1 Acceptance is executable behavior, not test-file presence](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-12-2 | [12.2 Backend and runtime matrix](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-12-3 | [12.3 Sabotage and mutation controls](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-12-4 | [12.4 Preventing removal, bypass, and false-green coverage](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-12-5 | [12.5 Failure reporting](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-13 | [13 Memory and performance measurement](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-13-1 | [13.1 No unsupported percentages](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-13-2 | [13.2 A real narrow regression—not a whole-compiler claim](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-13-3 | [13.3 Required metrics and attribution](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-13-4 | [13.4 Workload matrix](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-13-5 | [13.5 Admission budgets](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-14 | [14 Bug DB grouping and lifecycle integration](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-14-1 | [14.1 Canonical authority and representative groups](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-14-2 | [14.2 Representative mapping from reviewed reports](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-14-3 | [14.3 Proposed relation data—not a current schema claim](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-14-4 | [14.4 Migration procedure](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-14-5 | [14.5 Knowledge and recurrence workflow](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-15 | [15 Implementation work packages and rollout](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-15-1 | [15.1 Reuse existing owners](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-15-2 | [15.2 Work-package plan](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-15-3 | [15.3 Parallel development lanes](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-15-4 | [15.4 Rollout stages](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-15-5 | [15.5 Suggested policy configuration](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-15-6 | [15.6 Comparison with Rust and Java: what to emulate](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-16 | [16 Final release checklist](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-17 | [17 Sources and evidence register](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-17-1 | [17.1 Repository sources](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MEM-17-2 | [17.2 External primary sources](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) | memory_audit / root | OPEN |
| REQ-MCP-1 | [1 Requirements and fixed decisions](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-1-1 | [1.1 Non-goals for the first releases](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-1-2 | [1.2 Terminology](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-2 | [2 Inspected baseline and concrete gaps](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-2-1 | [2.1 Evidence standard](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-2-2 | [2.2 First audit deliverable](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-3 | [3 Architecture and ownership](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-3-1 | [3.1 Shared services, thin frontends](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-3-2 | [3.2 Logical library boundaries](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-3-3 | [3.3 Dependency and admission rules](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-4 | [4 Language providers](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-4-1 | [4.1 Capability levels](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-4-2 | [4.2 Provider matrix](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-4-3 | [4.3 Provider registration](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-4-4 | [4.4 SDN-specific work](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-4-5 | [4.5 SHS-specific work](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-4-6 | [4.6 Cross-language navigation](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-5 | [5 Snapshots, positions, and shared caches](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-5-1 | [5.1 Identity model](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-5-2 | [5.2 Coordinate rules](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-5-3 | [5.3 Unsaved buffers and external changes](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-5-4 | [5.4 Reuse the cache/SCV plan](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-6 | [6 Agent-session preferences](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-6-1 | [6.1 Proposed state](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-6-2 | [6.2 First-open and persistence rules](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-6-3 | [6.3 Toggle safety](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-6-4 | [6.4 SDN defaults versus session overrides](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-7 | [7 Source-view examples and folding](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-7-1 | [7.1 First file open without intent](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-7-2 | [7.2 Second file open](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-7-3 | [7.3 Navigation to a method](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-7-4 | [7.4 Intent-based open](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-7-5 | [7.5 Imports and non-block folding](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-7-6 | [7.6 Focus and reopen policy](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-7-7 | [7.7 Selection before serialization](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-7-8 | [7.8 The same view across languages](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-8 | [8 Compact help and navigation](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-8-1 | [8.1 Default footer](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-8-2 | [8.2 Essential help](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-8-3 | [8.3 Advanced help](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-9 | [9 Annotations, hints, and detail expansion](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-9-1 | [9.1 Boundary rule](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-9-2 | [9.2 Annotation catalog](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-9-3 | [9.3 Type and parameter hints inside code](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-9-4 | [9.4 Details](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-9-5 | [9.5 Independent toggles and footer](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-9-6 | [9.6 Line numbers when enabled](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-10 | [10 Diagnostics and safe automatic fixes](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-10-1 | [10.1 One canonical diagnostic path](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-10-2 | [10.2 Compact display and detail](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-10-3 | [10.3 Fix classification](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-10-4 | [10.4 Apply transaction](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-10-5 | [10.5 Concrete hardening in existing handlers](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-10-6 | [10.6 Diagnostics versus runtime failures](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-11 | [11 Source analysis for debugging](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-11-1 | [11.1 Shared query contract](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-11-2 | [11.2 Calls and references](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-11-3 | [11.3 Types](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-11-4 | [11.4 Writers and state changes](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-11-5 | [11.5 Control and data flow](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-11-6 | [11.6 Async/concurrency](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-11-7 | [11.7 Macro, generic, and aspect provenance](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-11-8 | [11.8 Combined debugging query](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-12 | [12 Debugging screen and shared REPL integration](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-12-1 | [12.1 One target authority](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-12-2 | [12.2 Proposed debugging screen](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-12-3 | [12.3 Assertion and test-runner flow](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-12-4 | [12.4 Stack trace policy](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-12-5 | [12.5 REPL operations](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-12-6 | [12.6 Dumps, server diagnosis, and hot replacement](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-13 | [13 Environment and configuration analysis](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-13-1 | [13.1 Four contexts, not one ambient environment](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-13-2 | [13.2 Proposed SDN artifacts](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-13-3 | [13.3 Inventory content](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-13-4 | [13.4 Configuration provenance](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-13-5 | [13.5 Container and OS context](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-13-6 | [13.6 Redaction and freshness](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-13-7 | [13.7 Example observed SDN record](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-14 | [14 Recent changes and regression analysis](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-14-1 | [14.1 Query semantics](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-14-2 | [14.2 Mapping and presentation](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-14-3 | [14.3 Passing-versus-failing comparison](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-15 | [15 MCP, LSP-MCP, LSP, and Neovim contracts](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-15-1 | [15.1 Small public tool families, shared typed operations](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-15-2 | [15.2 Example request and result](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-15-3 | [15.3 Result states and capabilities](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-15-4 | [15.4 LSP mapping and parity](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-15-5 | [15.5 External language-server broker](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-15-6 | [15.6 Neovim and the debugging screen](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-15-7 | [15.7 Integration with existing agent file readers](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-16 | [16 Editing and replacement transactions](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-16-1 | [16.1 Source-edit lifecycle](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-16-2 | [16.2 Editor and filesystem ownership](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-16-3 | [16.3 Verification after application](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-16-4 | [16.4 Live replacement is a separate operation](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-17 | [17 Performance and resource controls](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-17-1 | [17.1 Cheap views first, expensive facts on demand](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-17-2 | [17.2 Bounded work and output](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-17-3 | [17.3 Provisional performance objectives](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-17-4 | [17.4 Degradation behavior](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-18 | [18 Security and operational safety](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-18-1 | [18.1 Workspace trust and executable providers](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-18-2 | [18.2 Access boundaries](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-18-3 | [18.3 Safe rendering and data handling](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-18-4 | [18.4 Mutation and automation policy](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-19 | [19 Incremental delivery and ownership](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-19-1 | [19.1 Delivery principle](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-19-2 | [19.2 Binding relation to the shared debugger plan](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-19-3 | [19.3 Concrete initial backlog](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-20 | [20 Acceptance tests and release gates](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-20-1 | [20.1 Test policy](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-20-2 | [20.2 Required acceptance matrix](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-20-3 | [20.3 Representative end-to-end scenarios](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-20-4 | [20.4 Architecture enforcement](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-20-5 | [20.5 Release gates](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-21 | [21 Experiments and measurable outcomes](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-21-1 | [21.1 Source representation experiment](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-21-2 | [21.2 Operational success metrics](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-22 | [22 Migration checklist and risk register](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-22-1 | [22.1 Implementation handoff checklist](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-22-2 | [22.2 Risk register](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-22-3 | [22.3 Definition of done](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-23 | [23 References and evidence](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-23-1 | [23.1 Repository sources](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-23-2 | [23.2 Primary external references](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |
| REQ-MCP-23-3 | [23.3 Prior project design](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) | mcp_lsp_audit / source_view / root | OPEN |

## Memory executable acceptance

These exact IDs remain independent required rows. Each needs positive and negative controls where applicable, actual source-to-execution coverage, route/runtime identity, and evidence cardinality. Hand-built IR fixtures alone do not discharge them.

| Acceptance ID | Required scenario and oracle | Status |
|---|---|---|
| AC-OWN-01 | Default no-GC owner is moved on non-copyable assignment; second use is rejected  OPEN |
| AC-OWN-02 | Read-only and mutable short calls preserve the owner without hidden receiver allocation  OPEN |
| AC-OWN-03 | Explicit/tail return, field, optional, enum, tuple, array, map, and push transfers emit and execute one owner transfer  OPEN |
| AC-OWN-04 | Partial move, reinitialization, early-return branch, loop, and join cases behave correctly under block-order permutation  OPEN |
| AC-OWN-05 | Valid mutually exclusive paths compile; deliberately conflicting paths do not  OPEN |
| AC-BOR-01 | Returning/storing/caching a short borrow is rejected, even when a longer lifetime could theoretically make it safe  OPEN |
| AC-BOR-02 | Escaping closure, task, suspension, and asynchronous device submission cannot retain a short borrowed view  OPEN |
| AC-BOR-03 | Nested synchronous forwarding respects the original boundary; reentrant invalidation is prevented  OPEN |
| AC-BOR-04 | Long-lived owned lease plus repeated fresh short views works without widening a borrow  OPEN |
| AC-DROP-01 | Normal return, reassignment, scope end, error propagation, and cooperative cancellation clean each initialized owner exactly once  OPEN |
| AC-DROP-02 | Partial construction failure destroys initialized members only, in the defined order  OPEN |
| AC-DROP-03 | Observable resource cleanup order is unchanged by last-use optimization  OPEN |
| AC-FAIL-01 | Inject failure at every relevant allocation/registration/publication step; no unchecked store or partial success  OPEN |
| AC-CONT-01 | Fallible insertion and replacement preserve the documented owner on failure and commit it on success  OPEN |
| AC-CONT-02 | Clear/remove/drain release owned elements without requiring capacity to shrink  OPEN |
| AC-REG-01 | Inner scope cannot end an outer scope; failed begin does not confer scope ownership  OPEN |
| AC-REG-02 | Frozen retained roots survive scratch release; intentionally retained scratch references are rejected/detected  OPEN |
| AC-REG-03 | A resource-bearing arena runs required destructors; a dropless arena has no unnecessary per-node cleanup  OPEN |
| AC-HANDLE-01 | Freed/reused/wrong-owner/out-of-range/wrapped-generation handles fail resolution  OPEN |
| AC-CYCLE-01 | Region-owned cyclic graphs are valid and reclaimed with their owner  OPEN |
| AC-CYCLE-02 | Obvious shared strong-cycle risk is diagnosed in basic mode; ordinary weak/handle backedges are not mislabeled  OPEN |
| AC-CYCLE-03 | Deep/runtime budget exhaustion reports incomplete; runtime detection does not collect or mutate objects  OPEN |
| AC-CYCLE-04 | `cycle_check=off` does not disable mandatory move/drop/short-borrow checks  OPEN |
| AC-PIPE-01 | Fused and split produce equivalent semantics, errors, source locations, and required cleanup  OPEN |
| AC-PIPE-02 | Cold default path parses each exact parser input once; decode/replay and legitimate recovery are separately counted  OPEN |
| AC-PIPE-03 | Capture-off produces no debug checkpoint allocations/writes; targeted capture/replay remains functional  OPEN |
| AC-PIPE-04 | Cyclic imports, trait/default bodies, generic instantiation, static conditions, and layout dependencies stay correct  OPEN |
| AC-PIPE-05 | Failed or incomplete SCCs never become admitted executable/SMF success  OPEN |
| AC-CACHE-01 | Concurrent equal actions have one admitted producer; subscribers reuse the same immutable result  OPEN |
| AC-CACHE-02 | New edits do not change an in-flight snapshot; expired generations cannot publish  OPEN |
| AC-CACHE-03 | Eviction waits for actual reader quiescence; service crash cannot leave writable published artifacts  OPEN |
| AC-CACHE-04 | Changed imports, negative resolution, target, runtime ABI, grammar, aspects, or entry role invalidate the affected stage  OPEN |
| AC-HASH-01 | Inject equal XXH3 digests for different bytes/actions; no false cache hit or overwrite occurs  OPEN |
| AC-HASH-02 | Private-to-untrusted export uses the boundary's strong identity; algorithm/schema confusion is rejected  OPEN |
| AC-HASH-03 | Scalar/SIMD/pure/external hashing providers match canonical vectors and streaming/chunk boundary results  OPEN |
| AC-PROC-01 | Timeout, cancellation, parent death, worker crash, and spawn failure leave no surviving managed descendants or leaked reservations  OPEN |
| AC-PROC-02 | PID reuse and unrelated `simple` processes cannot be mistaken for managed children  OPEN |
| AC-BUDGET-01 | Parent/job limit reaches grandchildren; unknown measurements cannot enable unlimited worker fanout  OPEN |
| AC-BUDGET-02 | Queue/fiber/output/device-pin budgets work independently of worker count  OPEN |
| AC-METRIC-01 | Known allocations and process fixtures calibrate bytes/KiB/pages; missing metrics are unavailable, never zero  OPEN |
| AC-METRIC-02 | Repeated equivalent units show bounded scratch after warmup; intentionally retained artifacts are separately attributed  OPEN |
| AC-DB-01 | Group migration preserves every existing unrelated row/table and status; malformed/partial input causes no write  OPEN |
| AC-GATE-01 | Zero executed tests, omitted mandatory backend, or missing proof root cannot report PASS  OPEN |
| AC-GATE-02 | Removing/bypassing a checker, cleanup operation, or required test is detected by an independent gate  OPEN |

## Formal obligations

Proof roots require actual Lean build, transitive axiom audit and implementation refinement. Abstract proofs are not runtime/provider parity.

| Proof ID | Obligation | Implementation boundary | Status |
|---|---|---|---|
| FV-OWN-01 | Legal execution preserves one active unique owner and rooted ownership | Typed ownership events and move operations  OPEN |
| FV-OWN-02 | Uses of moved/uninitialized/dropped places are rejected | CFG analysis and place projection  OPEN |
| FV-BOR-01 | Every borrowed access is within its original short scope and live owner | HIR facts, call effects, runtime boundary  OPEN |
| FV-BOR-02 | Exclusive borrowing prevents conflicting access/owner invalidation | Place overlap, reentrancy, mutation contracts  OPEN |
| FV-DROP-01 | Cleanup is at most once; required initialized members are cleaned on supported exits | Drop elaboration and error/cancel edges  OPEN |
| FV-MOVE-01 | Fallible transfer either commits one owner or preserves the documented original owner | Containers, replacement, SFFI transfer  OPEN |
| FV-REG-01 | Region release cannot invalidate a surviving legal reference | Freeze/promotion/lease protocol  OPEN |
| FV-HANDLE-01 | Reused slots cannot validate an old owner/generation handle | Pool allocator and resolver  OPEN |
| FV-PIPE-01 | Fused/split schedules preserve defined results and cleanup order | Stage contracts and dependencies  OPEN |
| FV-CACHE-01 | A hit implies exact admitted input identity and complete semantic dependencies | Action keys, canonical identity and lookup  OPEN |
| FV-LEASE-01 | Eviction cannot race a valid active reader; expired producer cannot publish | Epoch/pin and task-generation state machines  OPEN |
| FV-FAIL-01 | Failure leaves no published partial success and no unowned reservation | Publication, task teardown, recovery  OPEN |

## MCP/LSP executable acceptance

Each selected matrix row requires its full scenario and oracle through the real public front door for promoted capabilities. Parser, registration or mocked-handler success is insufficient.

| ID | Scenario | Required observation | Status |
|---|---|---|---|
| VIEW-01 | First successful open for agent A | Folded outline, numbers off, Essential help once, minimal footer  OPEN |
| VIEW-02 | Second file and later navigation | No repeated first-use help; same preferences retained  OPEN |
| VIEW-03 | Two concurrent first opens | Exactly one first-help emission; both valid views  OPEN |
| VIEW-04 | Missing file, then successful open | Failure does not consume first-help state  OPEN |
| VIEW-05 | New subagent B | Independent defaults, help state, requester, and navigation  OPEN |
| VIEW-06 | Reconnect/resume and expired session | Authorized resume preserves state; expiry is explicit  OPEN |
| VIEW-07 | Retried `num` operation | Desired setting applied once, not toggled twice  OPEN |
| VIEW-08 | No-intent file open | All bodies folded; outline bounded; no accidental full-file dump  OPEN |
| VIEW-09 | Definition navigation | Target plus enclosing context revealed; siblings folded  OPEN |
| VIEW-10 | Import grouping, including noncontiguous imports | Accurate range sets, original ordering, relevant imports individually visible  OPEN |
| VIEW-11 | Folded block contains an error | Aggregate error visibility and detail navigation preserved  OPEN |
| VIEW-12 | `info`, `hint`, and `num` changed independently | No cross-setting changes or semantic-cache invalidation  OPEN |
| VIEW-13 | Source contains literal `\|`, `▌`, `/* */`, Korean text | Exact raw text preserved; decorations never stripped as source  OPEN |
| VIEW-14 | Long lines, tabs, CRLF, emoji/non-BMP text | Correct byte/protocol/display mappings; no split tokens  OPEN |
| VIEW-15 | Empty file | Valid empty snapshot and view, not read failure  OPEN |
| VIEW-16 | Bounded focused result omits necessary context | Explicit partial marker and functioning expansion handle  OPEN |
| LANG-01 | Simple valid and incomplete source | Native parser/query reuse; errors retain navigable spans  OPEN |
| LANG-02 | SDN comments, duplicates, schema errors, scalar groups | Source-preserving view; canonicalization does not erase evidence  OPEN |
| LANG-03 | `.shs` fixtures with sh/bash/native configuration | Correct dialect or explicit ambiguity; no execution on open  OPEN |
| LANG-04 | Shell parser imported with compiler frontend | Name-collision regression checked; no silent fallback labeled native success  OPEN |
| LANG-05 | C/C++ macro, conditional include, target flags | Syntax view works; semantic result tied to compile context  OPEN |
| LANG-06 | Rust cfg/features, generics, macro expansion | Provider context/provenance retained; executable expansion policy respected  OPEN |
| LANG-07 | Python imports, decorators, dynamic attributes | Static uncertainty preserved; module not imported to inspect it  OPEN |
| LANG-08 | Missing/broken foreign grammar or language server | Raw/structural fallback remains usable; missing semantics explicit  OPEN |
| DIAG-01 | Warning with successful compiler exit | Warning displayed; not incorrectly labeled wholly clean  OPEN |
| DIAG-02 | Analyzer timeout/crash/invalid payload | Analysis failure, not empty success or zero errors  OPEN |
| DIAG-03 | Windows drive path and escaped/multiline strings | Structured locations and messages round-trip correctly  OPEN |
| DIAG-04 | Multi-file labels and macro trace | Original provenance and all related ranges retained  OPEN |
| FIX-01 | Replacement is empty text | Valid deletion appears in preview and applies correctly  OPEN |
| FIX-02 | Multi-file/multi-replacement action | All replacements preserved with correct URIs and expected versions  OPEN |
| FIX-03 | Source changes after action creation | Stale fix rejected or explicitly re-resolved; no silent overwrite  OPEN |
| FIX-04 | Overlapping fixes or partial client application | Conflict/partial application reported; no false transaction success  OPEN |
| FIX-05 | Preferred but unsafe action | No unattended application based only on preference flag  OPEN |
| FIX-06 | Diagnostic disappears after analyzer failure | Not reported as verified repair  OPEN |
| FIX-07 | Unsaved editor buffer differs from disk | Correct owner/version edited; disk does not override buffer  OPEN |
| SEM-01 | Direct, recursive, method, indirect calls | Correct resolved/possible edges and explicit unresolved boundary  OPEN |
| SEM-02 | Shadowed variables and same-named members | Symbol identity prevents unrelated references/writers being merged  OPEN |
| SEM-03 | Alias write, field mutation, FFI side effect | May-write/effect distinction; unknown external effects retained  OPEN |
| SEM-04 | Branch-dependent assertion and loop | CFG/data dependence visible; no invented feasible execution claim  OPEN |
| SEM-05 | Concurrent access without sufficient ordering evidence | Possible race reported separately from observed event ordering  OPEN |
| HIST-01 | Last-touch, touches-in-window, net diff | Different semantics produce correct labeled results  OPEN |
| HIST-02 | Tag/ref moves after query creation | Frozen query remains pinned or explicitly refreshed  OPEN |
| HIST-03 | Rename, deletion, merge, shallow repository | Mapping/limitations visible; no fabricated current line  OPEN |
| HIST-04 | Worktree and unsaved changes | Distinguished from committed `~7d` changes  OPEN |
| ENV-01 | Installed compiler differs from actual build compiler | Inventory, selection, and observed invocation separated  OPEN |
| ENV-02 | Consumer-specific override beats general host value | Explanation follows actual owner precedence  OPEN |
| ENV-03 | Host and container have different PATH/OS/config | Correct execution scope; host facts not substituted silently  OPEN |
| ENV-04 | Secret values, denied probes, stale observations | Redaction, explicit denial, and freshness preserved  OPEN |
| DBG-01 | Interpreter test assertion | Stop before unwind; actual worker/fiber frame available through shared service  OPEN |
| DBG-02 | Screen, REPL, MCP inspect the same stop | Same debug identity, epoch, stack, locals, and source snapshot  OPEN |
| DBG-03 | Target resumes while detail request is in flight | Stale epoch rejected or frozen evidence explicitly returned  OPEN |
| DBG-04 | Actual target write triggers data watchpoint | Real writer location/event; not just debugger `set_variable` detection  OPEN |
| DBG-05 | Watch configured after earlier write | No invented historical writer or prior value  OPEN |
| DBG-06 | Optimized/stripped native executable | Missing/optimized-out/unwind limitations shown honestly  OPEN |
| DBG-07 | Fatal crash | Minimal capture path; no unsafe interactive REPL/upload in handler  OPEN |
| DBG-08 | Dump from different build/source | Mismatch flagged; read-only evidence not confused with resumable process  OPEN |
| DBG-09 | Session-local replacement | Running generation shown; old evidence retained; original test stays failed  OPEN |
| DBG-10 | Unsupported layout/ABI replacement | Typed rejection/restart requirement; no partial publish  OPEN |
| CACHE-01 | Many agents request same immutable result | Single production where configured; no mutable snapshot sharing  OPEN |
| CACHE-02 | Producer/waiter cancellation and failure | No poisoned entry, hung waiter, or false completed result  OPEN |
| CACHE-03 | Failed `.rr` metadata publication | No trusted partial graph; required consistency recheck completes before reuse  OPEN |
| CACHE-04 | Presentation-only toggle | No reparse/typecheck/build invalidation  OPEN |
| PROTO-01 | Real MCP/LSP lifecycle and malformed input | Correct framing/errors, bounded resources, clean shutdown  OPEN |
| PROTO-02 | Feature advertised but backend unavailable | Explicit unsupported/denied status; no placeholder answer  OPEN |
| PROTO-03 | Cancellation, paging, provider restart | Snapshot/version/cursor semantics retained  OPEN |
| SEC-01 | Path traversal, symlink escape, foreign detail handle | Access denied at the service boundary  OPEN |
| SEC-02 | Malicious comments/log instructions or terminal escapes | Treated as data; no tool execution or control-sequence injection  OPEN |
| SEC-03 | Two agents share a target | Authorized read access and serialized mutation lease; no accidental control transfer  OPEN |
| PERF-01 | 3,000-key stress, repeated open/close | Bounded memory, clean resource release, documented latency distribution  OPEN |

## Work-package and release obligation register

All WP-00 through WP-12 and rollout stages A–F from memory §15 remain required; all MCP phases P0–P9, tasks MCP-001–MCP-018, and companion debugger steps 0–4 from MCP §19 remain in scope. A vertical slice may land without satisfying later phases only when its claims and release evidence are explicitly bounded; the overall requested goal remains open.

### Memory final checklist

- MEM-REL-01: No-GC unique ownership is the actual default for ordinary owning references, not only a design statement or an `iso` test fixture. **OPEN**.
- MEM-REL-02: Short borrowing is unchanged in range; returning, storing, capturing, or suspending a borrowed view is rejected as specified. **OPEN**.
- MEM-REL-03: Every admitted execution route enforces the same ownership and cleanup rules. **OPEN**.
- MEM-REL-04: Transfer, partial initialization, container failure, and resource cleanup are correct on real execution paths. **OPEN**.
- MEM-REL-05: The Lean proof roots, assumption audit, and implementation-refinement checks pass within their stated scope. **OPEN**.
- MEM-REL-06: Fused compilation is the default; Parse/HIR/MIR/OBJ remain independently testable and replayable through the same implementations. **OPEN**.
- MEM-REL-07: Necessary global semantics and SCC completion are preserved; diagnostic objects do not count as admitted executables/SMFs. **OPEN**.
- MEM-REL-08: Disabled capture and runtime cycle tracing introduce no capture/edge-recording allocations in ordinary release execution. **OPEN**.
- MEM-REL-09: Phase scratch and resource-bearing regions reclaim correctly without dangling retained references. **OPEN**.
- MEM-REL-10: Immutable sharing reduces actual duplication; worker-local deserialization is measured, not mistaken for zero-copy sharing. **OPEN**.
- MEM-REL-11: Long sessions retire old unpinned generations and keep optional caches within explicit budgets. **OPEN**.
- MEM-REL-12: XXH3 private mode handles forced collisions correctly; untrusted boundaries use their strong identity/authentication policy. **OPEN**.
- MEM-REL-13: Cache keys include exact relevant semantic inputs without unnecessary global invalidation. **OPEN**.
- MEM-REL-14: Task failure cannot leave managed descendants, publication rights, pins, locks, or reservations behind. **OPEN**.
- MEM-REL-15: Metrics use correct units and distinguish payload, reserve, RSS, shared residency, and enforcement charge. **OPEN**.
- MEM-REL-16: The original affected integration/bootstrap route completes within its reviewed limits; reduced fixtures alone do not close it. **OPEN**.
- MEM-REL-17: Existing closed fixes remain protected; new bug relationships and verification scopes are recorded without rewriting history. **OPEN**.
- MEM-REL-18: Required proof/tests cannot be silently removed, skipped, replaced with source-only checks, or bypassed by an alternate route. **OPEN**.
- MEM-REL-19: Memory and performance comparisons use controlled workloads; residual costs and unsupported targets are disclosed. **OPEN**.

### MCP release and experiment obligations

- MCP-REL-01: P0–P2 truthfulness, source-map/session gates and real supported-language coverage (§20.5); OPEN.
- MCP-REL-02: P3 diagnostic/edit gates before fix capability promotion; OPEN.
- MCP-REL-03: Real stopped-target gates independently for each advertised debugger backend; OPEN.
- MCP-REL-04: Individually admit external semantic providers; grammar parsing is not semantic admission; OPEN.
- MCP-REL-05: Linux/Windows/macOS and applicable BSD/Simple OS lanes with explicit unsupported/unverified rows; cross-compilation is not execution; OPEN.
- MCP-REL-06: Scenarios A/B/C (§20.3), architecture enforcement and end-to-end provenance chain (§20.4); OPEN.
- MCP-EXP-01: Paired A/B/C/D/E representation experiment, isolated numbering comparison, fixed task/model/revision/budget controls, randomized trials, confidence intervals and failure categories (§21.1); OPEN.
- MCP-EXP-02: Actual versus claimed coverage, stale-edit rejection, expensive-compilation rate, cache hits, retained-session memory, first-help duplication, diagnostic fidelity, source/build mismatch detection and redaction metrics (§21.2); OPEN.
- MCP-REL-07: All migration checklist and risk-register conditions, same deployed-binary behavior, raw compatibility and complete definition of done (§22); OPEN.

## Closure authority

Root reviews every implementation/test mapping and exact candidate evidence, including negative controls, missing routes, proof roots and known residuals. Final completion also requires the reviewed PR(s) merged into `release/1.0.0`. No release tag or publication is requested. The canonical bug database remains authoritative; this requirement register is not a replacement tracker or bug-closure authority.
