<!-- codex-research -->
# UI Access Protocol — Feature Options

**Date:** 2026-04-15
**Feature:** `ui_access_protocol`

## Option A — Internal Protocol Only

### Description

Add a shared access protocol over `UISession` and `SurfaceManager`, expose it
through additive `/api/test/ui/*` routes and MCP tools, and package it through
repo-local plugin/skill docs.

### Pros

- matches current codebase architecture
- lowest implementation risk
- immediately useful for internal LLM/test tooling
- keeps one source of truth for Simple UI surfaces

### Cons

- no external desktop app introspection
- no screenshot fallback in v1

### Effort

- **M** — shared module, test API, MCP tools, docs, plugin, skill

## Option B — Internal Protocol + External Accessibility Adapter

### Description

Ship Option A plus a Windows-first UIA adapter that projects external desktop
windows into the same snapshot model.

### Pros

- closer to long-term desktop-agent goal
- validates the shared model against real external surfaces

### Cons

- large scope increase
- introduces platform-specific dependencies and unstable IDs
- distracts from the internal UI source-of-truth problem

### Effort

- **XL** — requires new adapters, error handling, perf, and docs

## Option C — Internal Protocol + Vision Fallback

### Description

Ship Option A plus screenshots, point-read helpers, or mark overlays.

### Pros

- gives a path for canvas/custom-rendered widgets
- improves debugging

### Cons

- extra latency and state-sync complexity
- less aligned with current repo foundations than semantic protocol first

### Effort

- **L** — new image capture and overlay flows

## Selected Option

**Chosen:** Option A with future extensibility for B/C.
