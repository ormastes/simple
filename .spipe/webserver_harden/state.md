# Feature: webserver_harden

## Raw Request
with spipe dev skill, harden simple os web server; small model-rated tasks, parallel agents, higher-model review after.

## Task Type
code-quality

## Refined Goal
The pure-Simple HTTP server (src/lib/nogc_sync_mut/http_server) enforces request limits (header count/size, request-line length, body/chunk size), rejects path traversal, and bounds slow clients, with specs for each rejection.

## Acceptance Criteria
- AC-1: Parser rejects request lines and headers exceeding configured limits with 400/431 and oversized bodies with 413; unit specs cover each limit at boundary and boundary+1.
- AC-2: Chunked-encoding decoding rejects malformed chunk sizes and overflow without panic; specs prove it.
- AC-3: Static/path routing rejects ".." traversal and absolute-path escapes; spec proves rejection.
- AC-4: Read path has a deadline/limit hook so a slow client cannot hold a handler forever; spec via injected limit (no live socket needed).
- AC-5: Existing http_server specs still pass in interpreter mode.

## Scope Exclusions
No changes outside src/lib/nogc_sync_mut/http_server/**, src/os/http/**, and their tests. No TLS work. No web_framework API changes.

## Phase
dev-done

## Log
- dev: Created state file with 5 acceptance criteria (type: code-quality)
