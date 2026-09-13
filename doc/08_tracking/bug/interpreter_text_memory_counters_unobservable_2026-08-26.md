# Interpreter text-memory counters are unobservable

**Status:** OPEN (unverified 2026-09-12)

## Status

Open observability blocker.

## Evidence

The runtime implements `rt_heap_live_bytes`, `rt_heap_peak_bytes`,
`rt_heap_alloc_count`, `rt_heap_aux_live_bytes`, and
`rt_heap_array_capacity_bytes`. The deployed interpreter registers only live,
auxiliary, and array-capacity functions; peak and allocation count fail as
unknown externs.

The registered functions returned zero before and after UTF-8 scanning, 4,096
scalar accesses, and UTF-16-to-UTF-8 conversion producing 16,380 output bytes.
Consequently, the zero values cannot prove zero allocation.

## Required resolution

Register peak and allocation-count externs in every interpreter/runtime
profile and make live/auxiliary/capacity accounting observe allocations made by
the exercised text representation. Add parity tests against native runtime
counters and a negative test proving that a deliberate allocation changes at
least one counter. Until then, receipts must use
`counter_status=unavailable` and retain isolated RSS/HWM evidence separately.

## Triage 2026-09-12

Status line inserted mechanically by the bug-db triage (record had no parseable `Status:` line); rule: filed before 2026-07-29 with no cheap repro → CLOSED-STALE, otherwise OPEN (unverified).
