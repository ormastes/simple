# Stage 3 transient promotion & deep-free planners hit hard `1 << 22` node cap

- **Date:** 2026-11-24
- **Status:** fixed
- **Fixed:** 2026-11-24
- **Severity:** P1
- **Area:** `src/runtime/runtime_native.c` (`RtCoreTransientPlan`, `RtCoreDeepFreePlan`)

## Symptom

During self-hosted Phase 3 full-compiler builds (`p3 -> p3`, compiling large `MirModule` graphs under transient heap scopes), `rt_core_transient_plan_push` refused node insertion once a promoted object graph exceeded `4,194,304` (`1 << 22`) nodes, causing transient scope promotion / deep-free planning to fail spuriously despite abundant host RAM and swap headroom.

## Root Cause

`src/runtime/runtime_native.c` hardcoded `#define RT_CORE_TRANSIENT_MAX_NODES ((size_t)1 << 22)` and `#define RT_CORE_DEEP_FREE_MAX_NODES ((size_t)1 << 22)` inside `rt_core_transient_plan_push` and `rt_core_deep_free_plan_push`. When a compiler phase retained a large object graph (more than `4,194,304` reachable strings/arrays/dicts/enums/raw allocations), `plan->cap * 2` crossed `1 << 22` and returned `0` even though `rt_observed_realloc_v1` could easily allocate the buffer. In addition, the resize/seen-set growth arithmetic needed `SIZE_MAX / 2`, `SIZE_MAX / sizeof(...)`, and overflow-free `rt_core_seen_needs_grow` threshold guards instead of wrapping `(seen_len + 1) * 10 >= seen_cap * 7` math.

## Fix

1. Removed `RT_CORE_TRANSIENT_MAX_NODES` (`(size_t)1 << 22`) and `RT_CORE_DEEP_FREE_MAX_NODES` (`(size_t)1 << 22`) from `src/runtime/runtime_native.c`.
2. Added explicit overflow checks (`plan->cap > SIZE_MAX / 2` and `next_cap > SIZE_MAX / sizeof(...)`) in `rt_core_transient_plan_push` and `rt_core_deep_free_plan_push`, plus the overflow-free `rt_core_seen_needs_grow` `size_t` threshold helper (replacing wrapping `(seen_len + 1) * 10 >= seen_cap * 7` checks) and `seen_cap > SIZE_MAX / 2` / `probe_limit` guards in `rt_core_transient_seen_insert`, `rt_core_deep_free_seen_grow`, and `rt_core_deep_free_seen_insert`.
3. Allocator out-of-memory (`rt_observed_realloc_v1` / `rt_observed_calloc_v1` returning `NULL`) continues to refuse atomically without partial mutation.

## Verification

- Reproducer & prevention test: `src/runtime/test/rt_transient_plan_unbounded_selfcheck.c`
  - Verifies `rt_core_transient_plan_push` and `rt_core_deep_free_plan_push` grow past `(1 << 22) + 1024` (`4,195,328`) nodes cleanly on x86_64 Windows (`clang.exe --target=x86_64-w64-windows-gnu`).
  - Verifies `SIZE_MAX` multiplication/doubling overflow rejection across both planners and their seen sets, plus `i686-w64-windows-gnu` `-fsyntax-only` compatibility.
- Real Phase 3 producer qualification: `C:/dev/p3_goal_20261116/stage3_from_s2/simple_stage3_srfix2.exe` built cleanly with the same runtime change and compiled full Stage 3 compiler groups without transient-plan cap refusal.
