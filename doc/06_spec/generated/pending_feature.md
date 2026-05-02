# Pending Features — Status Overview

**Generated:** 2026-04-04
**Source:** `doc/03_plan/30_pending_features.md`

## Implemented (Production-Ready)

| Feature | Status | Location |
|---------|--------|----------|
| LSP (Language Server Protocol) | **IMPLEMENTED** | `src/lib/nogc_sync_mut/lsp/`, `src/app/lsp/` |
| DAP (Debug Adapter Protocol) | **IMPLEMENTED** | `src/lib/nogc_sync_mut/dap/`, `src/app/dap/` |
| MCP (Model Context Protocol) | **IMPLEMENTED** (6 servers) | `src/app/mcp/`, `.mcp.json` |
| BDD Framework (SSpec) | **IMPLEMENTED** | `src/lib/nogc_sync_mut/spec/` |
| Doctest Framework | **IMPLEMENTED** | Integrated into test runner |
| LLM-Friendly Features (#400-410) | **IMPLEMENTED** | Context packs, AST/IR export, structured diagnostics |

## Still Pending

| Feature | Priority | Status |
|---------|----------|--------|
| Convention Documentation | Medium | Not started |
| TUI Framework | Medium | Not started |
| GUI Framework | Low | Not started |
| Web Framework (Rails-style) | Low | Not started |
| Package Registry | Medium | Not started |
| Property-based Testing | Medium | Planned (#406) |
| Snapshot/Golden Tests | Medium | Planned (#407) |
| Mutation Testing | Low | Not started |
| Fuzz Testing | Low | Not started |
| Incremental Compilation | Medium | Not started |
| Distributed Builds | Low | Not started |

## Notes

- LSP, DAP, and MCP were originally listed as "pending" but have been production-ready since 2026 Q1.
- BDD (SSpec) and Doctest were completed as part of the test infrastructure work.
- See `doc/06_spec/generated/feature.md` for the full implemented feature list.
- See `doc/03_plan/30_pending_features.md` for detailed descriptions of pending items.
