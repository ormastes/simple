# SSpec Documentization Maintenance — Agent Tasks

## Ownership

| Lane | Scope | Owner | Status |
|---|---|---|---|
| Architecture review | capsule boundaries, SPipe/EasyFix ownership | Codex design sidecar | complete |
| System-test review | traceability, fixtures, manual policy | Codex test sidecar | complete |
| Implementation | app capsule, CLI/MCP registration, tests | primary Codex | active |
| UI design | N/A — CLI maintenance tool; human output is captured as evidence | N/A | N/A |
| Merge owner | preserve concurrent work and integrate this lane | primary Codex | active |
| Final reviewer | `$verify`, including docs and stub scan | primary Codex | pending |

## Work packages

1. Implement typed findings, seven-dimension scoring, deterministic renderers,
   mirror inspection, and content-addressed identities.
2. Implement preview-first EasyFix application, rollback material, reference
   scaffold generation, and SPipe-owned documentization.
3. Register the command and MCP surface without changing legacy command behavior.
4. Add unit/integration/system/performance evidence and generate the manual.
5. Synchronize Codex/Claude/Gemini skills, test/refactoring guides, and LLM wiki.
6. Run the focused gates once, then production-readiness verification.

## Review decisions

The architecture sidecar required one discovery pass, path-independent finding
fingerprints, cache invalidation by all semantic inputs, and machine stdout
purity. The test sidecar fixed the five public step names and required fail-fast
generated scaffolds. These constraints are binding for implementation review.
