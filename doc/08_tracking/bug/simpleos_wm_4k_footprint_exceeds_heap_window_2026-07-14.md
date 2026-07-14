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

## Update (RESOLVED root cause + fix landed 2026-07-14, `1fe2653d`): it was an O(n^2) allocation, NOT heap sizing
The "scaling allocation / footprint > heap window" was a SYMPTOM. Actual root cause,
found by tracing FramebufferDriver.from_scanout_raw -> `_zero_u32_buffer(width*height)`:
that helper built the 4K back buffer with `buf = buf + [0u32]` PER ELEMENT.
Concatenation allocates a fresh array each iteration, so under the freestanding bump
allocator (no free) it allocated arrays of size 1,2,3,...,N = O(N^2) memory. For a 4K
back buffer (3840*2160 = 8.29M entries) it exhausts the heap after ~16K iterations
REGARDLESS of heap size — which is exactly why heap_off filled to heap_size at
192/320/336/512MB. FIX (landed `1fe2653d`): single `[0u32; count.to_i64()]` allocation
(33MB, once). VERIFIED: kernel builds, boots past framebuffer init, establishes the
real 4K scanout, engine2d-ready + keyboard/mouse-ready, and **`[PANIC] heap exhausted`
is GONE**. No memory-map or heap-size change was needed (all those experiments were
reverted). NOTE: `browser_backend.spl:196/224/315` have the SAME `buf = buf + [...]`
O(n^2) pattern — fix them too if their buffers can be large.

## Remaining blocker (separate bug): render-path null-deref, now UNMASKED
With the heap bug fixed, the WM boots to "mouse ready" then enters a tight fault loop:
355 EXCEPTION FRAME blocks, all `cr2=0x0` (null deref), cycling 3 RIPs
(0xb06732, 0xb07158, 0xb07b7e) each "recovered" and immediately re-faulted; harness
reports `guest-render-fault`, never reaches production-readiness/font-evidence, no PPM.
This `cr2=0x0` signature matches the ORIGINAL DrawIR-reroute regression (was rip=0x9ca634)
that the heap-exhaustion had been masking — i.e. the reroute left a null-deref in the
first-frame desktop render. This is the SimpleOS WM owner's render code (reliable
symbolization needs their own build). The O(n^2) heap fix is landed and independent;
this null-deref is what still blocks the 4K PASS.

## Update (2026-07-14): O(n^2) heap fix VERIFIED; render null-deref is compositor.spl failing NATIVE-BUILD (seed HIR)
The O(n^2) `_zero_u32_buffer` fix (`1fe2653d`) is CONFIRMED effective on a clean build:
two `[heap] alloc` lines total (~1MB early + one 0x800020 framebuffer alloc), boot
proceeds cleanly through pmm/vmm bootstrap, vfs-init, `framebuffer ready 3840x2160`,
engine2d-ready, keyboard-ready, mouse-ready — NO heap exhaustion. That regression is fixed.

Remaining blocker: the render null-deref (cr2=0x0 loop after mouse-ready) traces to
`compositor.spl` FAILING NATIVE-BUILD (passes `check`, fails `SIMPLE_BOOTSTRAP=1`), so
the kernel SKIPS it and links a weak-stub compositor → desktop-gui derefs a null
compositor entry → cr2=0x0 loop (RIPs 0xb05ea5/0xb06732/0xb07158/0xb1c529/...).
Native-build error: `hir: cannot infer field type while lowering
Compositor._handle_input_backend: struct 'ANY' field 'abs_x'`. Root: `inp` is the
`InputBackend` TRAIT, so the bootstrap HIR erases `inp.poll_mouse()`'s `MouseEvent?`
return to ANY, then rejects field access on ANY (07-12 compiled because native-build
then allowed ANY field access — a stricter HIR inference has since regressed it).
Workarounds tried + REVERTED (all still lower to ANY): type annotation, `if val`
pattern-binding (works for nilable FIELDS but not trait-method calls), correct field
names. Needs a SEED HIR fix (propagate trait-method return types) OR a concrete-backend
refactor — both bootstrap-scoped / WM owner's call. Same class as the web JIT gaps.

NET: O(n^2) heap bug FIXED+VERIFIED; full 4K PASS still blocked by the compositor
native-build failure.

## Update (2026-07-14): compositor native-build failure is a CLUSTER of seed limitations (pure-Simple workarounds exhausted)
Tried a free-function extractor workaround (pass the ANY-erased poll_mouse() result
to `fn _mouse_event_abs_x(ev: MouseEvent) -> i32`) — the typed parameter DID clear
the `struct 'ANY' field 'abs_x'` field-access error. But native-build then surfaced
MORE seed gaps in the same code, each a separate limitation:
- `ev.left_down()` and `ev.abs_x.to_i32()` METHOD calls lower to `const-0`
  placeholders (`[mir-lower] WARNING: unresolved method call ... lowered to const-0
  placeholder (silent-null risk, Task #145)`) — i.e. even if it linked, the mouse
  coords/button would be constant 0 (broken), because `ev.abs_x`'s result type is
  not propagated so the chained `.to_i32()` receiver is unresolved.
- inlining `left_down()` to `(ev.button_state & 1) != 0` cleared that one, but
  `to_i32` const-0 remained.
So the compositor is blocked by a CLUSTER of native-build MIR/HIR limitations
(trait-method-return ANY erasure + field-result-type non-propagation + method
const-0 placeholders), not a single idiom. All workarounds REVERTED. This is
seed-compiler (SIMPLE_BOOTSTRAP native-build) work — the same class as the web JIT
gaps. The O(n^2) heap fix (`1fe2653d`) stands and is verified.

## Update (2026-07-14): systemic — failed NVMe/FAT32 mount makes EVERY Fat32Core read null-deref
The font-load guard (`if g_vfs_mounted:` around gui_entry_desktop.spl's font read)
WORKS: the desktop now gets past the font load — `[desktop-gui] font unavailable
fallback=bitmap` → `compositor ready` → `shell initialized`, NO cr2 fault there.
But it exposed that the fault is SYSTEMIC, not per-call-site: immediately after
`[desktop-gui] spawn begin app=Browser Demo`, a NEW cr2=0x0 storm fires at the
app-registry spawn path — `app_registry_fat32_alias` / `app_registry_root_alias`
→ `Fat32Core.resolve_path`/`_device_read_sector` → `BlockDevice(NVMe).read_sector`
— the SAME null-deref chain at a DIFFERENT reader.

ROOT: on x86_64 the FAT32 mount fails (`[vfs] mount_failed fat32
reason=no-nvme-or-bad-fs`) but a non-nil `Fat32Core` wraps an uninitialized NVMe
`BlockDevice`, and `Fat32Core._device_read_sector` -> `dev.read_sector(lba)`
null-derefs (cr2=0x0) instead of returning its `Result<..., text>` Err. Every VFS/
app-registry consumer that reads through this broken mount crashes. Per-call-site
`if g_vfs_mounted:` guards are whack-a-mole (font load fixed, app spawn next, …).

CLEAN FIXES (VFS/NVMe owner): (a) make `NvmeBlockDevice.read_sector` /
`Fat32Core._device_read_sector` null-SAFE — return Err when the device/queues are
not initialized, so readers get an empty/None fallback instead of a fault; and/or
(b) leave `g_root_fat32 = nil` (not `Some(brokenCore)`) when the NVMe mount fails,
so the existing `if g_root_fat32 != nil` guards short-circuit everywhere; and/or
(c) fix the NVMe/FAT32 mount so it actually succeeds (the harness stages the disk;
`no-nvme-or-bad-fs` means the NVMe namespace/FS isn't being detected on this run).

NET SimpleOS WM 4K: advanced from boot-crash → boots through pmm/vmm/vfs/framebuffer/
4K-scanout/engine2d/input/compositor/shell-init (via `1fe2653d` O(n^2) + `3e5ef0c9`
compositor + this font guard); remaining blocker is the systemic null-deref on any
Fat32Core read against the failed NVMe mount — deep VFS/NVMe-driver work.
