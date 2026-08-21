# Agent Tasks: SFFI v2 Hardening

**Status:** P0/P1 implementation handoff; P4+ planned

## Frozen before fan-out

The primary/highest-capability owner freezes `SffiFunctionContractV2`,
`ReturnOrigin`, return families, `ForeignRaw`, error codes, ABI encoding,
system-spec helper names, and manual step text from the detail design. No agent
creates a private duplicate.

| Lane | Scope | Sidecar | Acceptance owner |
|---|---|---|---|
| A0 | schema, diagnostics, golden encodings | Codex Spark for census only | merge owner |
| A1 | Rust seed return and interpreter extern semantics | Claude Haiku for fixture inventory | merge owner |
| A2 | self-hosted frontend/HIR/semantics | Codex Spark for reference search | merge owner |
| A3 | generator and C/C++/Rust wrapper shapes | Claude Sonnet draft review | merge owner |
| A5 | JIT/native/linker/SimpleOS P0 closure | Codex Spark for lane census | merge owner |
| A7 | reproduce-first, system scenarios, parity | Claude Haiku for matrix census | final reviewer |
| P4–P6 | evidence, migration, full performance | planned; no sidecar starts yet | separately assigned |

Sidecars may inventory and draft bounded slices. They may not approve exclusions,
manual quality, generated evidence, or done marks.

## Integration order

1. A0 interface freeze and golden vectors.
2. A1/A2/A3 in non-overlapping owner files.
3. A5 consumes the frozen registry and error contract.
4. A7 reruns only previously RED/changed shards, then one authoritative matrix.
5. Documentation/bug records update from measured evidence.

## Ownership and review

- **Merge owner:** `/root` (or an explicitly reassigned primary agent).
- **Final reviewer:** best available normal/highest-capability Codex, independent
  of lower-model sidecar drafts.
- **Docs owner:** `/root/docs_specs` for this artifact set only.
- **Concurrent-work rule:** each implementation agent uses a separate worktree,
  commits only owned files, and reports unrelated dirt without folding it in.

Maximum three verify/fix cycles per phase. A lane with unavailable tooling
records a fail-fast blocker; it does not substitute seed/static evidence or a
passing placeholder.

## Current continuation sequence

1. Harden the three raw pointer-write providers and register exact void ABIs.
2. Enforce exact pointer-write declarations with a source audit; migrate all
   false return types and widened i32 payloads.
3. Add contract-bearing unsafe metadata and narrow `unsafe(ffi, raw_ptr)` call
   scopes, prioritizing wrappers that already establish allocation bounds.
4. Rebuild the contract inventory and migrate the next highest-risk uncovered
   runtime family.
5. Gate each slice with focused behavior, ABI, source, lint, and hot-path shape
   checks; do not repeat an already-green check in the same session.
6. Treat signing as separate artifact-admission evidence. Never label a
   provider semantically verified merely because its artifact is signed.
7. Linux `spl_winit` admission uses an open-file descriptor for both hashing
   and `dlopen`, with no hot-call work. Extend immutable-handle loading to
   other supported platforms before granting their sealed providers the same
   artifact-identity assurance.
8. Continue the inventory by replacing remaining sentinel/nullable raw ABIs
   with generated typed contracts and proof/test receipts; full SFFI remains
   incomplete until every execution lane consumes the authoritative registry.
9. Cocoa C/Rust providers and their Simple consumer are now fail-closed for
   fabricated presentation/blur success, invalid strings, and allocation
   arithmetic. Before `Verified`, run macOS real-provider race/sanitizer tests,
   bind the selected provider artifact, and replace ambiguous pixel/event
   sentinels with typed results.
10. Canonical `rt_sdl2_*` now owns O(1) generation-checked window resources,
    owner-thread gating, and validated pixel descriptors; app duplication is
    collapsed. Next replace the library owner's 66 generic unsafe contracts
    with exact per-function metadata and lexical wrapper scopes, then bind the
    dynamically loaded SDL artifact and sanitizer receipts before `Verified`.
11. SDL2 display discovery now returns typed absence instead of fabricated
    names/DPI/bounds and all 11 declarations have exact sentinels. Continue
    through the canonical event/input/clipboard declarations, then implement
    signed admission for the dynamically loaded SDL artifact.
