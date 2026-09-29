<!-- codex-design -->

# Dynamic runtime/kernel provider composition — parallel ownership

Date: 2026-09-22. Merge owner and final highest-capability reviewer: parent
Codex integration agent. Lower-model sidecars: N/A for this architecture lane;
the parent assigns already-authorized parallel implementation agents.

| Lane | Exclusive concern | Dependencies and handoff |
|---|---|---|
| P0 bootstrap authority | Actual runtime cdylib, dependency hashes, immutable capsule and candidate authority | Must land before claiming dynamic runtime bootstrap evidence |
| macOS Cocoa | Sole runtime dynload ownership of `rt_cocoa_*`, symbol table, typed failures, callback lifetime | Consume P0 authority; do not duplicate bootstrap ownership |
| native dynload | Cross-platform admitted mapping/query/callability, provider parity | Existing loader and SCI owners; report real mapped execution |
| aspect dynload | Binding-plan/mapping provenance, execution leases, final-unpin/quiescence bridge | Preserve unselected language options; never infer loaded advice from host callback |
| kernel/provider architecture | This additive architecture/TLDR, design and test/ownership plans | Documentation only; no active Cocoa/P0 source edits or builds |
| bootstrap supervisor | One bounded build/repair loop using immutable inputs and cached work | Wait for required source/authority snapshot; retain logs/hash and stop after three failed cycles |
| integration verifier | Review ABI/ownership boundaries, mutation evidence and native qualification | No broad done mark from leaf/unit/static PASS |

Shared interface vocabulary and record evolution rules are fixed in the
[detail design](../../05_design/compiler/dynamic_runtime_kernel_provider_composition_2026-09-22.md).
Shared `step(...)`, setup/checker helper names, fail-fast placeholders and
manual ownership are fixed in the
[test plan](../sys_test/dynamic_runtime_kernel_provider_composition_2026-09-22.md).
The implementation owner generates each mirrored manual; the integration
reviewer accepts its user-facing flow and zero-stub evidence.

## Migration gates

1. P0: demonstrate a cdylib-only mutation invalidates authority while unchanged
   archive content remains unchanged; fresh candidate uses the admitted bytes.
2. Cocoa: sole implementation symbols, successful real UI capability demand,
   zero optional initialization on no-demand startup, missing-provider failure.
3. Optional providers: coarse ABI seam and static/dynamic parity; record all
   retained dependencies and preserve selected K0/K1 classifications.
4. Cache and lifecycle: provider body/ABI/manifest mutations invalidate only
   their proven closure; pins and callbacks prevent premature retirement.
5. Aspect: select remaining requirement options when needed, then prove loaded
   advice origin, typed binding, native concurrency and owner-authorized release.
6. Promotion: platform and performance matrix, required MCP/LSP smoke and
   self-hosted bootstrap evidence. No release/push is part of this handoff.

Each lane records touched paths, exact commands and exit status, artifact
identity, native versus modeled evidence, and unresolved blockers. Preserve
other sessions' dirty files. A newly discovered choice returns to the parent
with pros/cons/effort; unrelated independent work continues.
