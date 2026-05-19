# SStack State: editor-ide-platform

## User Request
> impl 4 minimize duplication. with agent teams

## Task Type
feature

## Refined Goal
> Wire SVIM TUI and VSCode extension to share the existing editor backend (`src/lib/editor/`) and LSP server (`src/lib/nogc_sync_mut/lsp/`). Add missing editor features (multi-buffer, split panes, LSP client integration) to the shared backend, then have both SVIM and VSCode consume them — no duplicated logic in either frontend.

## Acceptance Criteria
- [x] AC-1: SVIM TUI uses `src/lib/editor/` piece-table buffer and document model (not its own)
- [x] AC-2: Shared editor backend gains multi-buffer manager (`src/lib/editor/30.views/`)
- [x] AC-3: Shared editor backend gains split-pane layout model
- [x] AC-4: SVIM TUI wires multi-buffer and split-pane through the shared backend
- [x] AC-5: VSCode extension has a language server client that talks to the existing LSP server
- [x] AC-6: No duplicated buffer/document/workspace logic between SVIM and VSCode
- [x] AC-7: Test specs exist for new shared editor components

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-10
- [x] 2-research (Analyst) — 2026-05-19
- [x] 3-arch (Architect) — 2026-05-19
- [x] 4-spec (QA Lead) — 2026-05-19
- [x] 5-implement (Engineer) — 2026-05-19
- [x] 6-refactor (Tech Lead) — 2026-05-19
- [x] 7-verify (QA) — 2026-05-19
- [x] 8-ship (Release Mgr) — 2026-05-19

## Phase Outputs

### 1-dev
Refined the user request into a clear goal with 7 ACs. Key insight: rich shared infrastructure already exists (`src/lib/editor/` with 15+ files, full LSP server with 19 files). The gap is wiring — SVIM uses its own buffer model, VSCode extension is scaffolding-only. Strategy: add missing capabilities (multi-buffer, split panes) to the shared backend, then wire both frontends to consume it.

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
