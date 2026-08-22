# Simple Lab pending events can grow without bound

Status: fixed 2026-08-22

## Problem

Every successful cell execution queued a `stream` frame and a `status` frame
in `LabApiSession.events`. The queue was cleared only when a client connected
to the session WebSocket endpoint. Repeatedly executing an existing cell does
not consume the per-session cell allowance, so a client that never opened the
WebSocket could grow this long-lived queue without limit. Each stream frame
could retain up to the configured 65,536-byte output limit.

## Fix

The session now owns a bounded ring. `SIMPLE_LAB_MAX_PENDING_EVENTS` controls
its capacity, defaults to 256, and is clamped to a documented ceiling of 1024.
Full-buffer writes overwrite the oldest slot in constant time. Frames larger
than `SIMPLE_LAB_MAX_WS_FRAME_BYTES` are dropped before enqueue, bounding both
the count and bytes retained by the queue without creating invalid truncated
JSON. Drain preserves retained-frame order and emits the architecture-required
`{"type":"resync","reason":"backpressure","dropped":N}` frame first when
frames were dropped. Drain then resets all ring state.

The WebSocket frame budget has a protocol minimum of 128 bytes. Both the
environment configuration and direct ring construction clamp to that minimum,
which fits a resync frame containing the largest signed decimal drop count.
The downstream WebSocket sender therefore never truncates a resync frame.

## Regression

`test/01_unit/app/simple_lab/pending_events_spec.spl` covers the storage bound,
drop count, ordered newest-frame retention, parsed resync notice, oversized
error-frame rejection, reset behavior, minimum-frame valid JSON, and
configuration default/clamping.
