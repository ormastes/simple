# UI CLI LLM Access Architecture — TLDR

T32 GUI access, Simple GUI/TUI, and host WM share one dependency-light command/result/error/safety grammar while keeping their existing semantic snapshots and source-owned execution.

## Core Shape

- `src/lib/common/ui/access_cli_grammar.spl` owns `AccessCommandDescriptor`, `AccessOperation`, `AccessRequest`, `AccessResult`, `AccessError`, `AccessSafety`, parsing, safety checks, and human/JSON rendering.
- `UiAccessSnapshot` and `WinTextSnapshot` remain the data models; no parallel CLI tree or history is added.
- `t32-cli`, `simple ui`, and `simple play` adapt overlapping list/snapshot/surface/find/act/history operations to the common grammar.
- UI live access uses the existing loopback `/api/test/ui/*` service; explicit DB fallback is stale-aware and read-only.
- Host WM and T32 keep enumeration, capture, refresh, and action execution in their owner adapters.
- Protocol v1 never exposes renderer state; optional v2 inspection must reuse `simple-draw-ir-v2` and stable component IDs from the canonical Draw IR P5/P6 plan.
- MDSOC weaving and a generic adapter registry are rejected: downward imports plus ordinary composition are smaller and acyclic.

## Operational Notes

- startup: help loads descriptors only; it does not contact a UI/T32 source, enumerate WM windows, open the DB, or load a renderer.
- hot path: one refresh/request per read; action performs one execution plus one observation; no per-window subprocess or scan.
- invalidation: source/session generation and snapshot revision reject stale targets; action invalidates only its affected source/surface.
- perf/RSS: warm list/snapshot p95 <= 100 ms, cached find/pre-action p95 <= 20 ms, CLI RSS delta <= 20 MiB, history <= 64 events.

## Open Next

- [Full architecture](ui_cli_llm_access.md)
- [Selected requirements](../02_requirements/feature/ui_cli_llm_access.md)
- [Detail design](../05_design/ui_cli_llm_access.md)
- [System test plan](../03_plan/sys_test/ui_cli_llm_access.md)
- [Common UI access source](../../src/lib/common/ui/access.spl)
