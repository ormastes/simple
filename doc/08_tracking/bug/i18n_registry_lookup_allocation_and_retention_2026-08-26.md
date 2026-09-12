# i18n registry lookup allocation and retention

**Status:** OPEN (unverified 2026-09-12)

## Evidence

The current thread-local nested-`HashMap<String, HashMap<String, String>>`
registry performs two allocations for every successful lookup: one for
`get_locale()` and one for the cloned result. A 4,096-message multilingual
catalog retains 958,791 tracked heap bytes. `clear()` leaves 308 bytes of outer
map capacity. See
`doc/10_metrics/text_i18n/i18n_registry_coverage_memory_2026-08-26.md`.

## Required fix

Replace hot lookup with explicit `LocaleContext` plus a compiled/static or
memory-mapped catalog returning borrowed message IR/data. The accepted hot path
must allocate zero bytes before formatting output. Reset/drop semantics must
state and test whether catalog capacity is retained or released.

## Acceptance gates

1. Successful and fallback lookup allocate zero bytes.
2. Catalog bytes/message and bytes/source-byte are reported.
3. Cold load, warm lookup p50/p95/p99, steady/peak RSS, and post-drop retained
   bytes are reported in the same native run.
4. Concurrent locale contexts do not use mutable process/thread global state.


## Triage 2026-09-12
No cheap repro attempted in this bulk pass (rule D: newer than 45 days, left open). Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
