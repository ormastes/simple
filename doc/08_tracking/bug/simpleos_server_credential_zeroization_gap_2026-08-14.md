# SimpleOS server credential zeroization gap

## Status

Open; release-blocking for production credential handling.

## Problem

The host disk builder wipes the transient buffer used to read the bounded
server credential after copying it into the ephemeral acceptance image. The
SimpleOS server then reads `/SYS/SRVDB.KEY` into immutable `[u8]` and `text`
values. The current target runtime exposes no proven secure-zero operation for
those copies after `CapabilityTable` registration.

## Required closure

Provide a target-owned secret buffer with bounded read, non-copying policy
registration or an owned move, and compiler-resistant zeroization at shutdown.
Verify that logs, receipts, crash output, and retained images contain no
credential bytes. Until then, use only ephemeral acceptance credentials,
restrict the generated image, and securely destroy it after the reboot probe.


## Triage 2026-08-17 — DEFERRED, blocker recorded

Reviewed in the lines 32-46 backlog sweep. Not actionable from this session: not a defect to re-verify but a MISSING RUNTIME PRIMITIVE: the record asks for
a target-owned secret buffer with bounded read, non-copying policy registration
or an owned move, and compiler-resistant zeroization at shutdown. That is a
runtime + language design change, not a bug fix, and its acceptance criterion
("logs, receipts, crash output, and retained images contain no credential
bytes") requires a SimpleOS boot with image inspection -- unavailable here. The
stated interim mitigation (ephemeral acceptance credentials only, restricted
image, destroyed after the reboot probe) remains the correct posture.

Status unchanged. Recorded so future sweeps skip this in O(1) instead of
re-deriving the same blocker.
