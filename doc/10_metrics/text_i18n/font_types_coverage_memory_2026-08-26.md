# Shared font types coverage and memory — 2026-08-26

The baseline configuration suite passed 5/5 at 39% branches (11/28) and 45%
lines (59/129). The focused branch matrix passes 5/5 and reaches 76% branches
(32/42) and 91% lines (118/129). It covers all validation fields, aliases,
supported categories and targets, plan failures/deduplication/policies,
caller-owned output, empty payloads/batches, material checks, and per-face versus
shared atlas ownership. The owner remains open after the three-cycle cap; no
100% claim is made.

The memory-performance smoke passes 1/1. Seven samples perform 1,792 execution
plans and length-delimited identity constructions: p50/p95 101,700/105,616 us,
process HWM 56,804 KiB, checksum 401,408. Execution was interpreter-demoted.
Allocation count/bytes, retained bytes, and linked-data bytes are unavailable,
so the observation does not satisfy a native joint time-and-memory row.
