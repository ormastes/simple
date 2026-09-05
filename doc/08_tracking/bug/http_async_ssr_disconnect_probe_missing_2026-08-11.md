# HTTP async SSR disconnect probe missing

## Status

Implemented prerequisite. Async-handler lifecycle cancellation now observes a
client FIN/RST while an HTTP/1.1 SSR job is pending through the worker-owned,
non-consuming `IoDriver.probe_tcp_peer` path.

## Current ownership and safety invariant

The worker is the sole socket reader. It submits a receive while parsing a
request, stops submitting receives after `RequestReady`, and resumes I/O only
after the async response completes. `close_connection` cancels and reclaims the
connection's async job exactly once.

Submitting a second receive merely to detect disconnect is unsafe: it can
consume pipelined HTTP/1.1 request bytes while the first response is pending,
removing those bytes from the connection parser and creating concurrent receive
ownership. Readiness alone is also insufficient because it cannot distinguish
queued application bytes from EOF.

## Minimal prerequisite

`IoDriver` needs a portable, non-consuming peer-state probe owned by its network
backend, for example:

```simple
enum TcpPeerProbe:
    Alive
    Closed
    DataPending
    Unsupported

fn probe_tcp_peer(fd: i64) -> TcpPeerProbe
```

The implementation must use non-consuming socket semantics (`MSG_PEEK` or an
equivalent backend facility), report FIN/RST separately from readable data, and
never create a second receive completion. Linux, SimpleOS, TLS, and fallback
backends must define the same result contract. `Unsupported` must retain the
existing bounded write-timeout behavior.

Once available, the owning worker can probe only fds in `async_job_by_fd` once
per event-loop iteration, call `close_connection(fd)` on `Closed`, and thereby
reuse the existing exactly-once lifecycle cancellation. The probe must be
bounded to the number of admitted async jobs and must not busy-poll outside the
normal driver iteration.

## Acceptance evidence

- A client that closes during a deliberately delayed SSR job releases its
  lifecycle slot before the SSR deadline.
- Pipelined bytes produce `DataPending` and remain available to the normal
  parser after the first response.
- No fd has more than one receive operation, including TLS connections.
- Unsupported backends retain timeout-bounded reclamation.

## Implementation evidence (2026-08-11)

- Host runtime peek regression distinguishes Alive, DataPending, preserved
  pipelined bytes, and Closed: 1 passed, 0 failed.
- Focused Simple contract spec verifies four-state mapping, bounded admitted-job
  iteration, close-only cancellation, no submitted receive, and the SimpleOS
  Unsupported fallback: 3 examples, 0 failures.
- SimpleOS intentionally returns Unsupported until its netstack exposes a real
  non-consuming peek; existing lifecycle deadlines remain authoritative there.
- A live delayed-SSR disconnect timing run still belongs to the admitted native
  web-server gate; this prerequisite no longer blocks that test.
