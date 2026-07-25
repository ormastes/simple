<!-- codex-design -->
# GPU Web and DB Offload Agent Tasks

Status: recovered design draft.

## Implementation Order

1. Add proxy state structures and worker operation constants.
2. Route `handler_type == "proxy"` to `start_proxy` before buffered handler dispatch.
3. Implement upstream lookup, round-robin selection, header rewrite, streaming, timeouts, and bounded buffers.
4. Add upstream connection reuse/pooling.
5. Add shared GPU batch descriptor/executor with CPU fallback and deterministic evidence backend.
6. Add web route GPU eligibility hooks.
7. Add DB planner eligibility hooks for scan/filter/project/vector search.
8. Add RAM-only GPU mode admission and fallback.
9. Add SSD-backed GPU mode with WAL/reopen/invalidation gates.
10. Add NoSQL/vector mode hooks and metadata-filter fallback.
11. Add SPipe system specs and generated manuals.
12. Add native/proxy and DB-mode performance evidence.

## Current Blocker

The current jj working copy reports unrelated unresolved conflicts in
`.spipe/gpu_containers_unified/state.md` and `src/app/cli/query_lint.spl`.
Source implementation should wait until those conflicts are resolved or the
user explicitly asks to implement in the conflicted checkout.
