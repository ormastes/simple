# SimpleOS formatted-input parser is unavailable
**Status:** OPEN (unverified 2026-09-12)

## Status

Guest libc now fails closed and supplies every declared formatted-input symbol.

## Fault and repair

`vsscanf` previously returned zero without parsing, while `scanf`, `fscanf`,
and `sscanf` were declared but had no guest providers.  The shim now returns
`EOF` and sets `ENOSYS` consistently for all four APIs.

## Unblock condition

Implement a bounded parser with exact conversion/assignment rules, overflow
handling, width limits, and a complete test matrix before promoting any of
these APIs.  Parsing untrusted configuration must not use this stub surface.

## Triage 2026-09-12
Rule D: record postdates 2026-07-29 and carries no short (<=3 min) repro; left open with a status line added since none existed. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
