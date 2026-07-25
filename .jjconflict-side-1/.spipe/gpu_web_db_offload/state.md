# Feature: GPU Web and DB Offload

## Raw Request

use spipe dev skill, off load process to gpu for thoughput and perf. improve web server, db server. 1. add full offloadable reverse proxy, to backed web process directly, 2. off load many logic to gpu in coarse grained in web and db. 3. db support ram only db and most gpu offload db. and ssd base but gpu accelerated. add nosql for gpu base db mode, reeearch deeply. use spark and normal llm and use agent teams for pherallel. see doc/01_research/lib/networking/reverse_proxy_gpu_boundary_2026-06-16.md

## Task Type

feature

## Refined Goal

Add a production-oriented Simple web/database acceleration architecture that implements CPU-owned reverse proxying and enables coarse-grained GPU offload for selected web and database workloads, including RAM-only, SSD-backed GPU-accelerated, and NoSQL/vector GPU database modes.

## Acceptance Criteria

- AC-1: Reverse proxy uses existing `ServerConfig.upstreams`, `LocationConfig.proxy_pass`, `UpstreamConfig`, and `UpstreamServer`.
- AC-2: Proxy locations use a worker-level streaming state machine, not a fully buffered synchronous content handler.
- AC-3: CPU workers own TCP accept, HTTP parsing, routing, proxy forwarding, backpressure, and response serialization.
- AC-4: GPU work is limited to coarse-grained web/database payload compute with CPU fallback.
- AC-5: DB support covers RAM-only, SSD-backed GPU-accelerated, and NoSQL/vector GPU database modes.
- AC-6: Reliability and CPU correctness gates come before GPU throughput claims.
- AC-7: SPipe specs discriminate GPU-hit from CPU fallback with real assertions.

## Scope Exclusions

- Do not make the GPU accept TCP, parse HTTP, own normal proxy forwarding, or replace DB durability/invalidation control paths.
- Do not claim production GPU speedup without baseline, fallback, and resource evidence.

## Phase

design-done-recovered

## Log

- recovery: Recreated lane state after current checkout no longer contained prior gpu_web_db_offload artifacts.
- recovery: Current jj working copy reports unrelated unresolved conflicts in `.spipe/gpu_containers_unified/state.md` and `src/app/cli/query_lint.spl`; this lane does not resolve or edit those files.

## Selected Scope

Feature Options B and C selected. NFR selection: Reliability Options 1 and 2 first; then Performance Options 1, 2, and 3.

Next phase: implementation and executable SPipe specs after unrelated jj conflicts are resolved or the user confirms working in this conflicted checkout.
