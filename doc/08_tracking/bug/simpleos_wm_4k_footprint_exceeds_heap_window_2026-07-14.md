# SimpleOS WM 4K regressed: DrawIR first-frame footprint exceeds the entire sub-384MB heap window

- **Status:** Open (regression; NOT fixable by heap sizing — needs OS-layout work)
- **Filed:** 2026-07-14
- **Area:** os / simpleos / x86_64 / baremetal-heap / WM-DrawIR
- **Severity:** high (blocks the 4K WM harness PASS that landed 2026-07-12 `603fabe601`)

## Symptom

`scripts/check/check-simpleos-wm-fullscreen-evidence.shs` regressed from PASS
(`603fabe601`, 2026-07-12: real 3840x2160 argb8888, baseline_ppm=24.9MB,
changed_bytes>0, sha256 round-trip) to FAIL after the "render SimpleOS WM through
DrawIR" reroute + hardening commits. The guest still BUILDS, BOOTS, and negotiates
a real 4K scanout (`[scanout-evidence] width=3840 height=2160 stride=15360
argb8888 generation=1`), then dies during framebuffer/VRAM-probe init, BEFORE
`production-readiness` / `font-evidence` / any PPM capture.

## Root cause (empirically bounded — this is the key result)

The x86_64 kernel uses a bump-allocator heap `_heap[]` (in `.bss`) sized by
`BAREMETAL_HEAP_SIZE` in `arch/x86_64/boot/baremetal_stubs.c`. The DrawIR reroute
raised the 4K first-frame working set past the old 192MB ceiling. Binary-searching
the heap size proved the footprint exceeds the ENTIRE usable heap window:

| heap | result |
|---|---|
| 192MB (origin) | `[PANIC] heap exhausted` |
| 320MB | exhaust — heap_off 0x13ff6a30, overshoot ~33KB |
| 336MB | exhaust — heap_off 0x14ff6790, overshoot ~35KB |
| 360MB | exhaust — heap_off 0x167f12f0, req 0x12b90, limit 0x16800000 (overshoot ~16KB) |
| 640MB | **triple fault** — `.bss` overran the FIXED boot page tables at 0x18000000 |

`.bss`/heap starts ~0x010be000 (~17.7MB). The boot page tables are at a FIXED
physical `0x18000000` (384MB) — logged as `root=0x18001000, pml4e0=0x18002807,
…`. So the heap MUST end below 0x18000000, i.e. max heap ≈ 367MB. At 360MB (the
largest heap that still fits below the page tables) it STILL exhausts during
init — and the TRUE footprint is even larger, since the panic precedes
maximize/restore/capture. **The window between "heap large enough for the 4K
footprint" and "collides with the fixed page tables at 384MB" is empty.**

## Why heap sizing cannot fix it

The 4K first-frame footprint is >360MB — roughly 10x the 33MB argb8888
backbuffer — which strongly implies the DrawIR reroute allocates many redundant
full-frame / intermediate buffers per frame in the bump allocator (no free within
a frame). No heap size below the 384MB page-table barrier can hold it.

## Fix directions (OS-layout / DrawIR — NOT a heap bump; owner: the SimpleOS WM session)

1. **Relocate or dynamically place the boot page tables ABOVE the heap** (or map
   them high) so `_heap[]` can extend past 0x18000000 into the 2G guest RAM. Then
   a larger heap can hold the footprint.
2. **AND/OR trim the DrawIR 4K allocation footprint** — a 4K frame needing >360MB
   (~10x the backbuffer) points at redundant per-frame buffer allocation in the
   canonical-DrawIR WM/font/web reroute; cap/reuse those buffers.

## Verification method (for whoever fixes it)
Run the harness with `SIMPLE_BIN=build/bootstrap/stage3/<triple>/simple` (the rust
seed is rejected). PASS = status=pass, baseline_ppm ~24.9MB, changed_bytes>0,
baseline_sha256==restored_sha256, over 2 consecutive reproducible runs.

## Provenance
Diagnosed 2026-07-14 by binary-searching the heap size against the harness (5
QEMU runs). The heap-size approach was tested and REVERTED (baremetal_stubs.c left
at origin 192MB) — it is provably not the fix. Supersedes the earlier "null-deref
cr2=0x0 rip=0x9ca634" signature, which the peer's hardening commits already
eliminated (the failure is now this heap-window overflow, not the null-deref).

## Update (refined 2026-07-14): TWO distinct problems — memory-map collision (fix verified) AND a scaling allocation (real blocker)

Two more QEMU-harness runs separated the regression:

### 1. Memory-map collision — root-caused, VERIFIED fix
`gui_entry_desktop.spl` spl_start(): `total_memory=512MB`, `reserved_end=384MB`.
`pmm_init_identity_range` places its bitmap + vmm page-table pool at reserved_end,
so kernel `.bss` (incl `_heap`) must end below 384MB; a heap grown past it collides
with the page tables (the 640MB-heap triple fault). FIX (tested — clean
`pmm-bootstrap:ok`/`vmm-bootstrap`/`memory-bootstrap:ok`, no fault): `total_memory`
512MB->2GB (QEMU -m 2G; crt0.s identity-maps first 4GiB), `reserved_end`
384MB->640MB so the page-table pool sits ABOVE the heap. 3-constant change.

### 2. Scaling allocation — the ACTUAL blocker (heap sizing cannot fix)
With the map widened (no collision) the WM STILL `[PANIC] heap exhausted` at
framebuffer init. Decisive: `heap_off` reaches EXACTLY heap_size every time —
319.96MB@320, 335.96MB@336, 511.98MB@512 — so a WM/compositor/DrawIR-init
allocation consumes ~ALL available heap, then a ~72-92KB alloc overflows. NO heap
size passes. `create_fb_engine_sized`->`BaremetalBackend.create_sized` only stores
fb+dims (no big buffer), so the culprit is deeper in the framebuffer-driver /
compositor-scene / canonical-DrawIR init the reroute added. Owner must find the
allocation sized from free/total/remaining heap (or an unbounded per-op loop) and
CAP it to a bounded frame budget. 07-12 PASS held the full sequence at 192MB — this
scaling is NEW with the reroute.

### Fix order (SimpleOS WM owner)
(a) cap the scaling allocation to a bounded budget; (b) apply the memory-map
widening only if the bounded footprint still needs >~360MB. My heap + memory-map
experiments were REVERTED (files at origin) — (2) is not heap-fixable.
