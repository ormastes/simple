# Engine3D owner partial coverage and memory — 2026-08-26

Owner: `src/lib/gc_async_mut/gpu/engine3d/engine.spl`  
Status: **OPEN / release-blocking**

The focused font compatibility specification reports 18/31 decisions (58%)
and 114/212 instrumented lines (53%). Six scenarios pass. The live neutral
glyph scenario fails before rendering with `semantic: unknown extern function:
rt_font_load`, so malformed/stale material and downstream live-font paths do
not close.

A five-spec invocation executed the font, CPU drawing, geometry, texture, and
pipeline files, but every child process wrote the same coverage path. The final
CSV therefore contained only the last pipeline process (0/1 owner decision)
and is not an aggregate artifact.

No attributable Engine3D memory result is available. The interpreter/test
closure does not expose owner allocation counters, and the failed font SFFI
path cannot produce canonical atlas, staging, upload, device-local VRAM,
post-eviction, or cleanup evidence. These values are `unavailable`, never zero.

Closure requires unique per-process coverage artifacts plus an identity-checked
merge, resolution of the canonical font-load SFFI path, all 31 static decision
outcomes, and a native CPU/Vulkan HUD/world harness reporting joint latency,
allocations, RSS, shared-atlas identity, staging/upload bytes, VRAM, and retained
memory after eviction and shutdown.
