<!-- codex-design -->
# GUI Design: KAIROS-Like Simple MCP + LLM Dashboard

Date: 2026-04-15

## Goal

Provide a browser/web dashboard view that mirrors the TUI mental model while allowing richer timelines, tables, and expandable task trees.

## Screen Structure

- top bar: session controls, attach/replay badge, freshness, policy mode
- left sidebar: session list and saved filters
- main center: timeline with grouped events and task-tree tabs
- right sidebar: digest, notifications, blockers, and bridge diagnostics

## Key Widgets

- live freshness badge
- wake reason pill set
- expandable child-task cards
- digest checkpoints list
- notification inbox with suppression reasons
- degraded-mode banner when live bridge is stale or absent

## Standalone Behavior

Without live MCP:

- replay/import banner shown
- control buttons visible but disabled
- snapshot provenance displayed

## Combined Behavior

With live MCP attached:

- controls route through documented MCP actions
- timeline appends deltas
- stale-state thresholds are visible to the operator
