# Architecture: Three-Tier Std-Lib (Core / Thin Host / Full)

Date: 2026-06-10. Status: adopted (plan:
`doc/03_plan/lib/host_io_layering/plan.md`; consumer plan:
`doc/03_plan/app/mcp_framework/plan.md`).

## Tiers

```sdn
tiers {
  core "src/lib/common/**" {
    contract "pure transforms; no I/O externs; no host/full imports"
    allowed  "pure value intrinsics (rt_sin, rt_sha256, ...)"
    gate     "scripts/check/check-core-lib-purity.shs (ratcheted baseline)"
  }
  host "thin wrappers over rt_*" {
    sync  "std.io_runtime + std.nogc_sync_mut.io.{file,process,dir,env}_ops"
    async "std.nogc_async_mut.host_io.{fileio,net,stdio} (HostFuture v1)"
    contract "1 extern + 1 wrapper fn per op; no policy/caching/logic"
  }
  full "core + host composition" {
    examples "http, db, mcp_sdk, net_server, fs trees, websocket, lsp"
    contract "imports core + host; apps import full (or host for tools)"
  }
}
```

## Rules (enforced)

- R1 Core purity: `src/lib/common/**` has no impure `rt_*` (file/dir/
  process/env/io/net/time/cli/exit/stdin) and no `nogc_*`/`gc_*` imports.
  Gate ratchets against `scripts/check/core_purity_baseline.txt` (14 files
  of recorded debt at adoption — shrink-only).
- R2 Host thinness: wrappers delegate or declare exactly one extern; the
  heredoc-shell `file_write` incident (fixed 2026-06-10) is the
  counterexample to avoid — host fns must not shell out for primitives.
- R3 App access: apps use facades only; `rg '\brt_'` gates in
  `check-mcp-native-smoke.shs` enforce per-app-dir zero direct runtime use.
- R4 No timeouts in idle paths: blocking reads are the idle state for
  servers (MCP stdio); startup gates bound startup, never idle.

## Why this shape

Startup: a thin host tier keeps eager import graphs small and interface
caches (SHB mtime fast path) effective — see the measured ladder in
`doc/07_guide/app/mcp/startup_performance.md`. Portability: core is
platform-free by construction; porting = re-implementing the host tier.
Testability: full-tier logic tests against in-memory/host fakes
(BufferTransport pattern).

## Current debt (recorded, ratcheted)

- 14 baselined `common/` files with impure externs or cross-tier imports
  (worst: `common/torch/dyn_sffi_*`, `common/compress/*` importing
  nogc compression internals — candidates to move INTO the proper tier
  rather than rewrite).
- Async host wrappers are eager-completing v1 futures (real HostFuture
  type, no thread offload yet); upgrade path noted in module docstrings.
- `rt_io_udp_bind` interpreter extern-scope gap (BUG-2 in the mcp plan).
