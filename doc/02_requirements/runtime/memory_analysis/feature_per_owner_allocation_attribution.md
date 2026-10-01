# Feature: per-owner allocation attribution (2026-07-29)

## Problem
Per-kind byte counters (L3, `rt_heap_live_bytes_by_kind`) say WHAT grew, not
WHO allocated it. When a counter shows "arrays +2 GB" the hunt for the source
is still manual. Rust closes this with heaptrack/bytehound/dhat call-stack
flamegraphs; that is the single biggest remaining gap in our memory infra.

## Proposal (phased)
- **P1 — owner tags at the choke point.** The interpreter/runtime already
  maintains `CURRENT_EXEC_MODULE` (+ function owner maps). On
  register/unregister in `runtime/src/value/heap.rs`, record bytes against the
  current owner: `Dict<owner, {live_bytes, peak_bytes, allocs}>` behind
  `SIMPLE_MEM_ATTR=1` (off by default; hot-path cost is one TL read + map
  bump). Externs: `rt_heap_live_bytes_by_owner()`, `rt_heap_top_owners(n)`.
  memstat/gate gain a `--by-owner` report.
- **P2 — sampled call-stack mode.** bytehound-style cheap unwinder, sampling
  1/N allocations (default N=64) to keep overhead <5%; dump in a
  heaptrack-compatible format so existing GUIs work.

## Acceptance
- P1: a fixture that allocates 10 MB from module A and 1 MB from module B
  reports A > B via `rt_heap_top_owners`; overhead with SIMPLE_MEM_ATTR unset
  is zero (feature-gated, counter path unchanged).
- Works under interpreter AND native (both backends) — attribution lives at
  the runtime choke point, not in codegen.

## Non-goals
Full always-on stack capture; PGHO feed (see backend-infra feature).
