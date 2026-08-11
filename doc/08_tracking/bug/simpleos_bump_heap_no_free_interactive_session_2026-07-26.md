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

## Companion finding: the 62MB allocations are LEGITIMATE (a wrong guess, corrected)

Both allocations are `sz=0x3b2c620` = 62,047,776 bytes from `rt_array_repeat`
(`caller=0x800a0b6` symbolizes to the `call malloc` inside it). Its size math
is `count*8 + 32`, so `count` = **7,755,968** elements.

I first argued this count had to be corrupted: it factors as
`2^6 * 11 * 23 * 479` and **no divisor pair resembles a screen rectangle** (the
nearest to the 3840-wide scanout gives 2019.78, and a full 4K surface would be
3840*2160 = 8,294,400). That reasoning was **wrong**.

The attribution receipt settled it on rerun36 — the real callers are:

| count | caller |
|---|---|
| 7,755,968 | `engine2d::backend_software::SoftwareBackend.init` |
| 7,755,968 | `engine2d::backend_software::SoftwareBackend.read_pixels_with_source` |
| 1,048,576 | `text_layout::font_renderer::FontRenderer._reset_font_atlas` |

These are real surface and glyph-atlas buffers, not corrupted lengths. The
factorization argument was numerology: "this integer has no pretty divisor
pair" is not evidence about a buffer whose size need not be a bare `w*h`.

**Lesson, and the reason the receipt existed at all:** the receipt was added
INSTEAD of acting on the inference, and it immediately refuted the inference.
Two other misattributions in the same campaign (a fake clock that was dead
code, and five reruns spent on a boolean-operand defect that was actually the
C5 enum-compare bug) came from acting on a strong prior without a control.

The receipt stays — it is cheap, silent below 1M elements, and it is the only
way to attribute a big repeat, because `[heap] alloc caller=` always resolves
to `rt_array_repeat` itself:

```
[array-repeat] big count=<n> caller=<return address>   # counts >= 1M elements
```

`caller=` is `__builtin_return_address(0)` of `rt_array_repeat`, symbolizable
with `nm <kernel.elf>`.

Because the allocations are legitimate, sizing does NOT become unnecessary —
per-frame reclamation is the only real fix, and every render genuinely costs
~124MB of unreclaimed surface until it lands.

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

## Re-verification (2026-08-10)

Status confirmed unchanged: `free()` in
`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` is still
a no-op bump allocator (checked the current file). The root fix (per-frame
reclamation with a separated retained/frame-local allocation path) is C
runtime work exercised only through `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`
(SimpleOS x QEMU/board lane) — both editing the baremetal C allocator and
re-running the QEMU/board evidence lane are out of this sweep's scope (no
`bin/simple build bootstrap`, and this sweep is a `.spl`-source doc-tracking
pass, not a hardware/QEMU verification pass). No `.spl`-source workaround
exists because the defect is in the freestanding C allocator itself, not in
compiler-generated code. Leaving **OPEN — ARCHITECTURAL** (requires baremetal
C allocator redesign + fresh QEMU/board evidence, out of scope for this
sweep). The 512MB mitigation remains landed and is not further downgraded.
