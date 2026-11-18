# slang model load takes 64-120 s regardless of model size (Windows)

Observed 2026-11-15 by `slang_model_variety_live_spec.spl` (logs `build/probe/variety_cpu_1.log`,
`build/probe/variety_gpu_1.log`): `engine_ensure_loaded` took 64-120 s for every model on both CPU
and Vulkan lanes, including the 270M gemma (Q8_0, ~0.3 GB) at 76-85 s and the 7B at 64-98 s. Load
time does not scale with file size, so it is a fixed overhead, not weight reading.

Suspected cause (not yet proven): `check_fit` in
`src/lib/gc_async_mut/slang/model_executor/model_loader/memory_budget.spl` probes memory with
`shell_int("powershell -NoProfile -Command \"(Get-CimInstance Win32_OperatingSystem)...")`, a
PowerShell spawn that is slow on a loaded Windows host (another agent is already reworking this probe).
Needs a timed breakdown of probe vs `load_model` vs `open_context` to confirm.

Also seen: GPU gemma-3-270m generation (2 tokens) 3271 ms vs 1218 ms on CPU; cold Vulkan
pipeline compile on the first request after load is the likely reason; no warm-up request was made.

## Resolution (2026-11-18 — Wave C2)

Status: fixed

Confirmed in `llm_engine.spl` (`check_fit(..., default_headroom_bytes())`): every model load on
Windows spawned two PowerShell CIM processes — `Win32_OperatingSystem.TotalVisibleMemorySize` in
`mem_total_bytes()` and `Win32_PerfFormattedData_PerfOS_Memory.AvailableBytes` in
`_win32_available_bytes()` — adding 54-135 s of fixed probe overhead per load under host contention.

Fixes landed:
1. `src/lib/gc_async_mut/slang/host/slang_host.spl`: added `slang_windows_available_bytes_fast()`
   backed by SOSIX `sosix_windows_memory_headroom_v1()` (`GlobalMemoryStatusEx`, `<1 ms`),
   returning `0` off Windows or when the snapshot returns `Err` / `<= 0`.
2. `src/lib/gc_async_mut/slang/model_executor/model_loader/memory_budget.spl`: routed
   `_win32_available_bytes()` through `slang_windows_available_bytes_fast()` first with PowerShell
   CIM retained only as fallback, and memoized positive `mem_total_bytes()` results in
   `_cached_mem_total_bytes` (with `reset_mem_total_cache_for_test()`).
3. Regression coverage added in `test/01_unit/lib/gc_async_mut/slang/host/slang_host_spec.spl`.
