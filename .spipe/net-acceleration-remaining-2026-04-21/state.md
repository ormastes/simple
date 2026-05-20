# SStack State: net-acceleration-remaining-2026-04-21

Feature: net-acceleration-remaining-2026-04-21
Phase: 8-ship
Cooperative: solo (plan already written)
Source plan: doc/03_plan/agent_tasks/net_acceleration_remaining_2026-04-21.md

## User Request

Implement remaining net acceleration work: TCP socket behavior, async HTTP server
capability routing, packet I/O boundary API, and hardware acceleration stubs.

## Task Type

Feature implementation — net stack, TCP state machine, HTTP server capability gates,
packet ring ownership, SR-IOV/RDMA scaffolding.

## Refined Goal

Provide correct socket-visible TCP behavior (connect completion, data path, FIN/RST),
route HTTP static file responses through capability gates, define packet ring ownership
API with explicit RX/TX buffer semantics, and stub hardware acceleration discovery
(SR-IOV VF assignment, RDMA transport).

## Acceptance Criteria

- [x] TCP connect completion returns ESTABLISHED, timeout, refused, or unreachable
- [x] TCP recv has blocking/would-block semantics; send has window-aware queuing
- [x] FIN, RST, TIME_WAIT surface to socket callers
- [x] HTTP worker routes SendFile through sendfile gate; portable fallback wired
- [x] Worker startup records backend name and acceleration tier
- [x] Packet ring RX/TX ownership is explicit and testable
- [x] SR-IOV discovery hooks defined (opt-in, isolation-gated)
- [x] RDMA transport config scaffolded (explicit-only, no auto-select)
- [x] 20 spipe tests pass covering all 4 source modules

## Phase Checklist

- [x] 1-dev (Developer Lead) — 2026-05-18
- [-] 2-research — skipped (plan doc comprehensive, prior session research complete)
- [-] 3-arch — skipped (architecture captured in plan and net_backend.spl)
- [-] 4-spec — skipped (acceptance criteria in plan serve as spec)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA Lead) — 2026-05-18 (20/20 tests pass)
- [x] 8-ship — 2026-05-18

## Log

- 2026-05-18 dev: Scoped to 4 modules — tcp_connection_behavior, socket_connect_semantics,
  http_capability_router, packet_ring_ownership. 20 spipe tests created and verified.
- 2026-05-18 impl: Created 4 source .spl files and 1 test spec file with 20 tests.
- 2026-05-18 verify: All 20 tests pass in interpreter mode.
- 2026-05-18 ship: Files committed, state closed.

## Pipeline Status: CLOSED — verified Wave 16-1
