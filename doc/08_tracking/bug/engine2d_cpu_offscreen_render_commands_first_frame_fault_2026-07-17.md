# Engine2D CPU-rasterizer offscreen/embedded-batch first-frame fault storm

Status: Open.

Date: 2026-07-17

## Status

Open. Found by the RENDER-STABILITY lane on the SimpleOS x86_64 desktop
(`examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`) after
fixing the font-renderer facade-mutex fault storm (see
`font_renderer.spl` fix in the same session — `_font_mutex_acquire`/
`_font_mutex_release` no longer fault). This is a **separate, downstream**
fault storm that now fires during the very first frame composition, before
`[desktop-gui] first-frame-rendered` ever prints.

Corroborated by a prior (scanout) lane's independent finding in
`render_findings.md` (session scratch notes, not committed):
"Boot serial = the PAINT signature (NOT composition-fault): `20x [fault]
cr2=0x0` then `engine2d-draw-ir-rejected reason=auto selected cpu ...
rendered=0 skipped=5` ... composition builds fully (guards work) and the sole
remaining blocker is the Engine2D CPU-rasterizer paint." That lane flagged it
as out of scope for its own (WM-composition-path) task; this doc gives it a
permanent home.

## Evidence

Build: `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl` via
the canonical recipe in
`scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs`
(`--backend cranelift --cpu x86-64-v1 --opt-level=aggressive --mode dynload
--entry-closure --target x86_64-unknown-none --linker-script
examples/09_embedded/simple_os/arch/x86_64/linker.ld`), booted under
`qemu-system-x86_64 -machine q35 -cpu max -m 2G` with an NVMe-backed FAT32
disk (mount fails: `[vfs] mount_failed fat32 reason=no-nvme-or-bad-fs`, so
this reproduces even fully offline from any font/VFS asset).

Serial sequence (clean, post font-renderer-mutex fix):

```
[desktop-gui] font unavailable fallback=bitmap
[desktop-gui] compositor ready
... shell/spawn/launcher lines ...
[wm-frame] host-gpu-fallback reason=unavailable-or-readback-capacity width=3840 height=2160
HOST_GPU_NEGOTIATION_DONE ... result=fallback backend=software ...
[dbg-vbe] pre-first-frame xres=3840 yres=2160 ...
[heap] alloc sz=0x800020 off_before=0xa56f40 caller=0x80107a6
[heap] alloc off_after=0x1256f60
... (9 total allocations of exactly 0x800020 bytes, ~8MB each) ...
[heap] warn: crossed watermark off=0x9261400

[fault] *** EXCEPTION FRAME ***
[fault] rip=0x00000000088a97bc
[fault] cr2=0x0000000000000000
[bt] ra=0x00000000088b23c8
[fault] *** END FRAME (recovering) ***
... repeats 15x, then ...
[PANIC] heap exhausted
[PANIC] heap_off=0xc000000 req=0x20 limit=0xc000000
```

`rip` resolves (via `nm -n build/os/_wk/desktop.elf`) to
`lib__gc_async_mut__gpu__engine2d__draw_ir_adv___engine2d_draw_ir_render_commands`
(offset ~0x3ac / ~940 bytes into the function); the backtrace return address
resolves to
`lib__gc_async_mut__gpu__engine2d__draw_ir_adv___engine2d_draw_ir_render_batch_embedded`.
Both files: `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`.

The 9x ~8MB allocations immediately preceding the fault match the shape of
per-embedding CPU offscreen-surface buffers described in
`_engine2d_draw_ir_render_batch_embedded`'s docstring ("renders into a fresh
offscreen Engine2D sized embedding.width x embedding.height ... then the
finished surface is stitched into `engine`"). `cr2=0x0` is a genuine
null-pointer dereference (not the C8 code-bytes-as-address signature).

DIAG-instrumented rebuild (temporary `print()` bracketing added then reverted
around the `DRAW_IR_COMMAND_TEXT` branch in `_engine2d_draw_ir_render_commands`,
lines ~501-535) showed **no** `[DIAG-T] enter text command` marker before the
fault, and the fault's offset into the function was unchanged (~928-940 bytes
both with and without the added prints) — so the crash is not inside the text
command branch specifically; it happens earlier in the same function, most
likely in the per-command loop's RECT branch or in the embedded-batch/offscreen
surface setup that precedes real command dispatch, and is unrelated to
font/glyph availability.

## Impact

The first real frame never renders (`rendered=0` per the prior lane's note);
each "recovered" fault leaks/consumes heap (matching the documented
fixed-2-byte-RIP-advance fault-recovery defect in
`doc/08_tracking/bug/simpleos_native_build_entry_closure_codegen_defects_2026-07-17.md`),
eventually exhausting the 192MB heap and panicking before
`[WM] Glass desktop rendered!`/`first-frame-rendered` ever prints. This is the
current blocker for a non-black QMP screendump of the glass desktop.

## Required fix

1. Instrument `_engine2d_draw_ir_render_commands` and
   `_engine2d_draw_ir_render_batch_embedded` with `print()`-based markers per
   command index / per embedded-surface allocation (not gated to the TEXT
   branch) to find the exact command/allocation that faults.
2. Check whether the embedded-surface offscreen `Engine2D` construction (or
   the "Preserve the nested Draw IR struct layout across the native
   free-function boundary" workaround mentioned in
   `_engine2d_draw_ir_render_batch_embedded`'s own comment) is passing a
   corrupted/nil struct across the native free-function boundary under
   `--entry-closure --opt-level=aggressive` — this smells like the same
   family of struct-passing/anon-tuple-return codegen defects (C4 in the
   entry-closure defects doc) rather than a Simple-level logic bug.
3. Root-cause and fix, or add a defensive freestanding-safe skip (skip the
   embedded/offscreen compositing path and paint directly, matching how
   `_wm_draw_ir_text`'s `else: draw_ir_text(...)` bitmap fallback already
   soft-fails font unavailability) if the real fix requires compiler-level
   changes out of this lane's scope.
