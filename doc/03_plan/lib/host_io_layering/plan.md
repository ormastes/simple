# Plan: Three-Tier Std-Lib Layering with Async NoGC Host I/O Wrappers

Date: 2026-06-10
Status: draft (research done, tasks divided)
Driver: user goal — "net, fileio, stdio: async nogc thin host std lib wrapper;
refactor core lib / small host lib thin wrapper / full lib; make MCP use std
lib with no timeout."

## 1. Research Summary (what exists today)

- Layer model (`doc/07_guide/language/lib_architecture.md`): `common/` (pure),
  `nogc_sync_mut/` (sync I/O + rt forwarding), `nogc_async_mut/` (task/fiber
  scheduling, **no async I/O**), `gc_async_mut/`, `nogc_async_mut_noalloc/`.
- Thin host forwarding already exists but is **sync-only and scattered**:
  - `src/lib/nogc_sync_mut/io_runtime.spl` — canonical thin rt_* wrapper
    (file, process, env, dir, time, exit, args; used by 21+ app files).
  - `src/lib/nogc_sync_mut/io/{file_ops,process_ops,dir_ops,env_ops,...}.spl`
    — richer per-area facades.
  - `src/lib/nogc_sync_mut/mcp_sdk/transport/stdio.spl` — MCP stdio framing
    (`mcp_stdio_read_message`, Content-Length / JSON-lines auto-detect),
    blocking, no internal timeout.
- `nogc_async_mut/async_host/` (future, scheduler, waker, worker_thread,
  joinset, ...) provides task machinery but no net/fileio/stdio bindings.
- MCP servers (`src/app/mcp`, `src/app/simple_lsp_mcp`, ...) now route all
  runtime access through `std.io_runtime` facades (rt-forward feature, AC-1).
  Startup gate: `scripts/check/check-mcp-native-smoke.shs`, 5000 ms max,
  interface-cache + rt-forward cache validity checked.
- Closed prior art (do not duplicate): `.spipe/lib-naming-consistency`
  (canonical names), `.spipe/loader-shared-core-refactor` (loader invariants).

Conclusion: the user's three-tier idea matches the existing direction; the
right move is to **consolidate**, not invent a parallel hierarchy. The gap is
(a) one named thin host-wrapper surface, (b) async variants for net/fileio/
stdio built on `async_host`, (c) MCP transport consuming the std surface with
no arbitrary timeouts.

## 2. Target Architecture

```
+--------------------------------------------------------------+
| full lib  (std.*)  — core + host-backed functionality        |
|   http, db, mcp_sdk, fs trees, redis, websocket, lsp, ...    |
+-----------------------+--------------------------------------+
| core lib (pure)       | host lib (thin wrapper)              |
| src/lib/common/*      | std.host.{fileio,net,stdio,proc,env} |
| text/json/math/crypto | sync: delegate io_runtime/io/*_ops   |
| protocol logic, codecs| async: nogc futures via async_host   |
+-----------------------+--------------------------------------+
|              runtime (rt_* externs, C/Rust seed)             |
+--------------------------------------------------------------+
```

Rules:
- R1 Core lib never imports host lib or rt_*; pure transforms only.
- R2 Host lib is *thin*: 1 extern + 1 wrapper fn per operation; no logic,
  no policy, no caching. Sync fns delegate to existing `io_runtime`/`io/*_ops`
  (no duplication); async fns return `Future`-compatible handles scheduled on
  `nogc_async_mut.async_host`.
- R3 Full lib composes core + host; apps import full lib (or host lib
  directly for low-level tools) — never rt_* (enforced by rg gates, as in
  check-mcp-native-smoke.shs).
- R4 MCP transport: blocking stdio read is the protocol idle state, never
  wrapped in a timeout; per-request work has no library-imposed timeout.
  Startup stays under the existing 5000 ms gate via interface-cache fast path.

## 3. Tasks (parallel-ready, disjoint scopes)

Wave 1 — host lib surface (parallel Sonnet agents):
- T1 `std.host.fileio`: new `src/lib/nogc_async_mut/host_io/fileio.spl`
  (+ async read/write/stat via async_host worker offload; sync delegates to
  io_runtime/file_ops). Spec: `test/01_unit/lib/host_io/fileio_async_spec.spl`.
- T2 `std.host.net`: `src/lib/nogc_async_mut/host_io/net.spl` — async
  connect/accept/read/write over existing tcp/udp sffi facades
  (`nogc_sync_mut/io/tcp.spl`, `udp.spl`). Spec: `net_async_spec.spl`
  (loopback echo).
- T3 `std.host.stdio`: `src/lib/nogc_async_mut/host_io/stdio.spl` — async
  line/byte reads feeding a waker; sync delegates to existing stdio surface;
  reusable by MCP framing. Spec: `stdio_async_spec.spl` (pipe-driven).

Wave 2 — consumers + audit (after Wave 1 lands):
- T4 MCP on std lib, no timeout: mcp_sdk transport consumes `std.host.stdio`;
  remove/avoid any read timeout in server loop; keep smoke-check startup gate
  green; extend `check-mcp-native-smoke.shs` with a no-timeout assertion
  (server idle > gate without exiting).
- T4a Wrapper probe cache (measured 2026-06-10: wrapper handshake 2722 ms =
  native 1361 ms ×2 because `mcp_probe_native` runs a full initialize +
  tools/list against the candidate before exec'ing it again). Cache probe
  success keyed by binary path+mtime+size under `.simple/cache/`, re-probe
  only on change; update the wrapper *generator* (scripts/setup) not just
  bin/ copies. Expected ~50% startup win — the largest single lever; see
  `doc/07_guide/app/mcp/startup_performance.md`.
- T4b Lazy tool registry: `initialize` response must not require building
  151 tool schemas; build on first `tools/list` or serve a build-time table.
- T5 Core-purity audit: rg gate that `src/lib/common/**` has no `rt_` and no
  imports from nogc_* layers; fix violations (move to host/full layer).
- T6 Docs: `doc/04_architecture/lib/host_io_layering/` + tldr; update
  `lib_architecture.md` with the three-tier mapping table.

Wave 3 — convergence (sequential):
- T7 Migrate remaining app-level direct rt_* users (beyond MCP, e.g. other
  src/app tools) to facades, dir by dir, gated by the same rg pattern.

## 4. Acceptance Checks

- A1 `std.host.{fileio,net,stdio}` import + run in interpreter mode; async
  specs pass in interpreter mode (compiled-mode caveats documented).
- A2 No new extern duplication: each rt_* extern declared once in the host
  wrapper layer (`rg 'extern fn rt_' src/lib | sort | uniq -d` clean).
- A3 `check-mcp-native-smoke.shs` passes including startup < 5000 ms and the
  new idle/no-timeout assertion.
- A4 Core purity gate green for `src/lib/common/**`.

## 4a. Follow-on plan

Network-server lib + MCP framework + app migration continues in
`doc/03_plan/app/mcp_framework/plan.md` (Waves A–D, parallel Sonnet tasks).

Known limitation found in Wave 1 (T2): `rt_io_udp_bind` is not registered in
interpreter mode when reached via the `nogc_async_mut → nogc_sync_mut/io/udp`
module chain (plain `UdpSocket.bind` fails the same way in that context).
Live UDP assertions are skipped with a concrete reason in
`test/01_unit/lib/host_io/net_async_spec.spl`; needs an interpreter
extern-registration fix in the udp lane.

## 5. Risks

- Interpreter-mode extern hangs in std modules (known stdin issue) — keep the
  inline-transport fallback until `std.host.stdio` proves stable in both modes.
- Async I/O on worker threads must not regress nogc guarantees — host wrappers
  stay allocation-light; no GC layer imports.
- Parallel agents need disjoint dirs (one dir per agent; io_runtime.spl owned
  by a single agent per wave).
