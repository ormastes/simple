# ISA registry architecture — D0

Status: authored design; runtime/typecheck/docgen UNRUN. Base: a9cf82179cd3f0212a46b39d63032a788d8196b8.

Authority: existing REQ-MC-009 in `doc/02_requirements/language/mission_critical_profile.md`, D0 in `doc/03_plan/agent_tasks/mission_critical_robustness_parallel_agents_2026-07-27.md`, and research §7.1–7.2 in `doc/01_research/language/simple_vs_rust_mission_critical_2026-07-27.md`. This design implements the selected registry slice; it does not redefine those requirements or claim backend conformance.

## Boundary and ownership

`src/app/isa_registry/model.spl` owns data contracts; `parser.spl` owns bounded strict decoding and typed validation; `generator.spl` owns deterministic presentation and verification obligations. Dependency direction is generator → parser → model. Parser internals are sibling-private. No compiler dispatch/backend changes, external process, environment lookup, network call, implicit discovery, global mutable state, or new toolchain. Normal src-root imports and the existing pure-Simple runner apply.

A small static module pipeline is sufficient. A plugin registry, runtime composition, cross-cutting MDSOC transform and cache would add lifecycle/invalidation concerns without an established workload. Each call owns its input and output. Caller-owned pinned authority is explicit, never inferred from registry contents. Future consumers must separately enforce critical-profile build rejection for unsupported/unverified lowering.

## Trust and completeness

IsaAuthority carries ISA identity, specification revision, whole snapshot SHA256 and the complete extracted canonical operation ID set. Registry metadata must match it exactly, and its rows must equal that set, without duplicates. A digest-shaped string is identity, not authentication: the eventual integration artifact must retain provenance, original snapshot, extraction procedure and reviewed full set. Empty authority is rejected as unknown universe. Synthetic test IDs have no architectural meaning and cannot close D0.

Catalogue completeness, callability, lowering declaration and certification remain distinct. All research fields and native/synthesized/library/llvm/unsupported/unverified states survive parsing. Verification names are required evidence kinds, not test outcomes. Empty encoder/decoder declarations are preserved; no blanket encoder rule is inferred for library/LLVM/synthesized rows. Unsupported/unverified require a reason. The critical registry profile requires fallback=forbidden without outlawing explicitly named lowering strategies.

## Data flow

1. Check explicit limits and source byte length before decoding.
2. Decode a closed versioned SDN record, preserving duplicate-key detection before map construction.
3. Validate field types, enum vocabulary, bounds, metadata, row uniqueness and exact authority membership.
4. Sort copies by canonical operation ID for coverage; sort each set-valued list for stable output.
5. Emit declared coverage and independent (operation ID, evidence kind) obligations. No percentage or certification inference.

Limits are capacity guards, never truncation or an instruction denominator. Reject oversize input during scanning/allocation; do not parse first and measure later. Complexity target is O(bytes + (rows + authority IDs) log(rows + authority IDs) + list sorting), bounded memory O(input + rows + output). Benchmark startup/latency/RSS after runtime qualification; no unmeasured performance claim or numeric target is invented here. No cache means no stale-cache invalidation path.

## Completion gates

Fixture acceptance establishes parser/generator behavior only. Full D0 additionally needs user-selected authoritative ISA/revision, complete pinned extraction, real registry artifact, generated coverage wired into the actual consumer, and qualified runtime evidence. Reference/FLS and per-instruction backend certification remain separate lanes. User selection is pending; routine contract implementation and strict fixture tests proceed independently.

See `doc/05_design/isa_registry.md` for frozen API and wire contract and `doc/03_plan/sys_test/isa_registry.md` for traceability.

## SDN compatibility decision

The canonical `src/lib/common/sdn/parser.spl` handles configuration maps/arrays and provides `parse_with_issues` for duplicate-key detection. Duplicate preservation alone does not justify a separate reader. Its dispatch has no tagged parenthesized research-record form and its lenient generic decoding does not expose this contract's pre-allocation text/list/row bounds. The bounded private registry reader implements only the explicitly frozen tagged wire grammar; it is not another SDN implementation or toolchain. Reference/FLS may use canonical maps independently. Interoperability with canonical SDN requires an explicit future grammar/API decision; no language short-form compiler defect was observed or silently worked around here.
