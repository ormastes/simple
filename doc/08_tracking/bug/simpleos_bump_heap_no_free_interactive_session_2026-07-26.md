# SimpleOS x86_64 bump heap never reclaims — the FIRST interaction after boot panics "heap exhausted" (2026-07-26)

Status: OPEN (mitigated by sizing, root fix not implemented)
Lane: `scripts/check/check-simpleos-wm-fullscreen-evidence.shs` (SimpleOS-WM x QEMU showcase cell)

## Symptom

The WM evidence lane reached its capture stages for the first time on rerun35
and died on the very first injected keypress:

```
[wm-loop] polling-active
[wm-input-irq] input_seq=1 scancode=87 kind=press
[wm-input-irq] input_seq=2 scancode=215 kind=release
[web-scan] ... np=22 ...
[web-style-producer] entries-ready count=1 len=86
[heap] alloc sz=0x3b2c620 off_before=0x4c357f0 caller=0x800a0b6
[heap] alloc off_after=0x8761e10
[heap] alloc sz=0x3b2c620 off_before=0x87685e0 caller=0x800a0b6
[PANIC] heap exhausted
[PANIC] heap_off=0x87685e0 req=0x3b2c620 limit=0xc000000
```

Host side: `capture.out` = `guest-input-press-state-frame-correlation-missing
action=maximize`, verdict `capture-input-or-guest-correlation-failed`.
`baseline.ppm` captured fine (24.8MB, valid magic); `fullscreen.ppm` and
`restored.ppm` were never written.

## Root cause

`free()` in `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c`
is a no-op — the allocator is a pure bump pointer over a static `_heap[]`.
Nothing is ever reclaimed, so allocations are permanent **for the whole
session**, not for the frame that made them.

Boot plus the first desktop frame legitimately reach ~142MB (`off_before=
0x4c357f0` is already 79MB before these two allocations, and the pre-existing
watermark warning in `malloc` documents "legitimately allocates past 144MB").
The heap was 192MB. So the first re-render after boot — any interaction at all
— had ~50MB of headroom and needed 124MB.

**This makes the failure structural, not incidental: with no reclamation, the
guest can serve exactly one frame per boot.** The maximize path was never
reachable, which is why 34 prior reruns never executed a capture stage.

## Mitigation landed

Heap raised 192MB -> 512MB (warn watermark 144 -> 448MB). The identity map
covers 4GiB (`crt0.s` `boot_pd`, 2048 x 2MiB pages) and the lane's VM has 2GB,
so 512MB of `.bss` is both mapped and physically present.

Sizing only buys a bounded number of renders. It is not a fix.

## Root fix (not implemented)

Per-frame reclamation. The frame path is the only large allocator, so a frame
arena is the natural shape: record `_heap_off` before a WM frame renders and
restore it after the frame is presented, so frame-local buffers die with the
frame.

The blocker on doing this blind: anything allocated during a frame that must
OUTLIVE it (glyph atlases, cached scene/material state, retained surfaces)
would be corrupted by a reset. Landing this safely needs those lifetimes
separated first — a retained/long-lived allocation path distinct from the
frame-local one — otherwise the reset silently frees live objects and the
failure mode becomes corruption rather than an honest panic.

## Companion finding: the 62MB allocation is itself suspicious

Both allocations are `sz=0x3b2c620` = 62,047,776 bytes from `rt_array_repeat`
(`caller=0x800a0b6` symbolizes to the `call malloc` inside it). Its size math
is `count*8 + 32`, so `count` = **7,755,968** elements.

That count factors as `2^6 * 11 * 23 * 479`, and **no divisor pair resembles a
screen rectangle** — the nearest to the 3840-wide scanout gives 2019.78. A
legitimate full-screen surface would be 3840*2160 = 8,294,400. So the count
looks like a corrupted length crossing a channel, in line with the other
channel-loss defects on this lane, rather than a real surface allocation.

An attribution receipt now names the .spl-level caller:

```
[array-repeat] big count=<n> caller=<return address>   # counts >= 1M elements
```

`caller=` is `__builtin_return_address(0)` of `rt_array_repeat`, symbolizable
with `nm <kernel.elf>`. Needed because the `[heap] alloc caller=` field always
resolves to `rt_array_repeat` itself and cannot identify the real site.

If the count is confirmed garbage and fixed, per-render cost collapses and the
heap sizing question largely goes away.

## Also sighted (pre-existing, diagnostic-only here)

```
[web-scan] builtin-divergence k=15 np=22 ... index_of_builtin=2305843009213693951 index_of_portable=3
```

`2305843009213693951` = `0x1FFFFFFFFFFFFFFF` — a tagged-nil sentinel leaking
through `(seg.index_of(">") ?? -1) as i32` on the freestanding lane: the
nil-coalesce does not fire and the `as i32` does not truncate. Same class as
`native_to_i64_nil_coalesce_print_tagbox_leak_2026-07-20.md`. **Not** the cause
of this panic — the scan itself uses the portable `find_from`, so the builtin's
result is only compared, never used. The divergence receipt did its job.
