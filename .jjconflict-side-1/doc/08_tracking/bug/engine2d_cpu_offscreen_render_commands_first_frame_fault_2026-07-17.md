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

## ROOT-CAUSED (2026-07-18, ENGINE2D-FAULT lane) — it is a class-method
## receiver-binding miscompile in the FONT path, NOT the engine2d offscreen path

**The offscreen/embedded-batch/`cr2=0x0`/C4-struct-passing framing above is
superseded.** Re-run of `gui_entry_desktop.spl` with the current seed
(`src/compiler_rust/target/bootstrap/simple`, 07-17 14:25) into `build/os/_wke2d/`
(vfs skip kept `if true:`, NVMe attached) reproduces the storm and it was chased to
the exact faulting instruction with `nm`+`objdump`.

### The storm is one first-frame fault, mis-recovered into ~71-81 cascades
- The `build/os/_wk` evidence ELF was built with an OLDER seed; its serial has **no
  `cr2=0x0` anywhere** — every `cr2` is code-bytes (`0x244c8d4c7500c6xx`, +8/iter) or
  small-negative. Those are pure `+2`-RIP-recovery derailment (C8-CLOSE only hardened
  `#UD`; this is a `#PF`, still recovered → cascade). Fault COUNT (81 vs 71 vs 66) is
  cascade noise and must not be used as a fix signal — use the FIRST fault + screendump.
- Fresh build (current seed): first fault `decode_string+0x3b <- rt_string_trim+0x15`
  during first-frame text (after `[dbg-vbe] pre-first-frame`, before any
  `first-frame-rendered`); screendump 3840x1092 non-black 25.01% (the doc's 12.64% was
  the old build). ud2-halt never fires ⇒ `#PF`, not a literal `ud2`.
- The bug-doc `rip=0x88a97bc` actually resolves to `_engine2d_draw_ir_style_value+0x3c2`;
  `render_commands+0x3a0` is a `ud2` after `call rt_eprintln_str` = the compiler's
  "field access on nil receiver" panic (a derailment landing spot, not the primary).

### CONFIRMED root cause (disassembly, `build/os/_wke2d/desktop.elf`)
In `resolve_font_metrics_with_language` (`font_renderer.spl:1453`):
```
  call *rcx        ; rcx=&font_render_config_default_for_size ; config returned in RAX  (OK)
  movabs $0x8a74f30,%rdi   ; rdi = &FontRenderConfig.identity   <-- callee address
  call *%rdi        ; config.identity()   -- RAX (the config) is NEVER moved into RDI
```
`FontRenderConfig.identity`'s prologue reads `self` from `rdi` (`mov %rdi,%rax; and $-8`).
So `self` = the method's OWN code address; `self.family` loads the prologue bytes
(`sub rsp,0x3a0` = `48 81 ec a0 03 …`) as a string data pointer → `.trim()` →
`decode_string` dereferences a code address → fault (`cr2` = those code bytes, hence it
CHANGES with code layout). **A class-instance method call (`config.identity()`,
`config.valid()`) under `--entry-closure --target x86_64-unknown-none` binds `self` to the
callee's constant address instead of the receiver — the receiver value in RAX is dropped.**
It is an INDIRECT/duck-dispatch call (`movabs addr,%rdi; call *%rdi`) that conflates the
`self` register with the call-target register. Reached from BOTH the render path
(`engine.draw_text_with_advances` → `font_execution_plan(config)` → `config.valid()`) and
the metric path (`resolve_font_metrics_with_language` → `config.identity()`). Free-function
calls are unaffected — `font_render_config_default_for_size(font_size)` gets its arg in RDI
correctly (target goes in a separate reg). Hosted builds render fine.

### Disproven fixes (do NOT re-try — verified inert against the first fault + screendump)
- **static→free** for `FontRenderConfig.default_for_size(...)` at `engine2d/engine.spl`
  (font_types.spl:162 documents the static path call as miscompiled): first fault and
  25.01% UNCHANGED. `default_for_size` returns the config fine either way; the bug is the
  downstream `config.identity()/valid()` method dispatch.
- **typed intermediate `val`** for the chained `.identity()` at `_resolved_font_metric_language_key`:
  inert — `resolve_font_metrics_with_language:1454-1455` ALREADY uses `val config = …;
  config.identity()` and faults identically. Receiver shape (temporary vs typed val) is not
  the axis; the method-dispatch is.

### Fix direction (seed codegen defect; pure-Simple workaround = free functions)
Convert `FontRenderConfig.identity()` / `.valid()` from instance methods to free functions
`font_render_config_identity(config)` / `font_render_config_valid(config)` and pass `config`
as an explicit typed argument at every call site (no receiver dispatch). A minimal seed fix
would correct the method-call lowering that loads the callee address into the `self`
register. Defensive floor for degraded-no-disk (task option 3): guard the text/metric entry
points (`draw_text_with_advances`/`draw_shaped_text` lack `draw_text`'s `has_sffi_ttf()`
fail-close) so no config method is invoked when no face is loadable.

### Fix APPLIED + VERIFIED (2026-07-18)
`src/lib/nogc_sync_mut/text_layout/font_types.spl`: `FontRenderConfig.identity()`/`.valid()`
converted from instance methods to free functions `font_render_config_identity(config)` /
`font_render_config_valid(config)`; all 8 call sites in `font_types.spl`/`font_renderer.spl`
updated to pass `config` as a typed argument (no receiver dispatch). `engine2d/engine.spl`
NOT changed (the static→free attempt was inert and reverted).

Clean rebuild (666 compiled, 0 cached) + QEMU boot (`gui_entry_desktop.spl`, vfs skip kept,
NVMe attached), `build/os/_wke2d/`:
- **Font-config method-dispatch storm ELIMINATED: 81 recovered faults → 1.** Serial 951 → 151
  lines; the render now progresses further (per-embedding 8 MB offscreen surfaces allocate) and
  the boot no longer hits `[PANIC] heap exhausted` — the storm's heap-eating `rt_string_concat`
  cascade is gone.
- **Frame completion NOT yet reached**, however: there is still no `first-frame-rendered` /
  `[WM] Glass desktop rendered!` marker. The serial ends with ONE remaining fault then goes
  silent: `render_commands+0x3a0` = the compiler's "field access on nil receiver" `ud2` panic
  (`call rt_eprintln_str; ud2`), `cr2=0x0` — a genuine null-field deref. Disasm: an indirect
  `call *rax` inside `render_commands` returns nil, the result (`r12`) is untagged and its
  offset-0 field is read (`mov (%r12),%r14`) → fault. This is a SEPARATE, pre-existing defect
  (the C4-addendum "nil command field / nil-returning call reaching render"), NOT the
  method-dispatch storm — left as a distinct follow-up.
- Screendump 3840x1092 non-black 25.01% is a PRE-COMPLETION capture (the frame never reached
  its completion marker), so it is not a reliable "fully-composited desktop" figure; it is
  unchanged from the pre-fix current-source boot. NOTE: 12.64%→25.01% is old-build-vs-current-
  source, NOT this fix's effect — the fix's win is storm/heap-PANIC elimination, not pixels.

Evidence: `build/os/_wke2d/serial.log` + `screendump.ppm`; nm/objdump traces in the lane
scratchpad (`nm_fix4.txt`, disasm of `resolve_font_metrics_with_language` / `identity`).

## LAST-FAULT lane (2026-07-18) — render_commands+0x3a0 nil-command fault ROOT-CAUSED + FIXED

**The remaining `render_commands+0x3a0` fault is FIXED. Zero faults now.** It was NOT
the receiver-binding miscompile again and NOT a backend Option-None; it was a genuine
null `DrawIrCommand` array element produced by *unannotated command-producer functions*
whose erased returns corrupt a mixed `[DrawIrCommand]` array literal under `--entry-closure`.

### Disassembly (evidence ELF `build/os/_wke2d/desktop.elf`, md5 96d20f2c)
`_engine2d_draw_ir_render_commands` (`draw_ir_adv.spl:482`, `for command in commands:`):
```
  88b1846: call *rax        ; rax=rt_index_get(commands, i)  -> element -> [rsp+0x7f0]
  88b185a: call *rcx        ; rt_pool_safepoint()  (GC, irrelevant)
  88b1871: call *rax        ; rax=rt_native_neq(element, r14=3)  = `command.? == false` -> `element == 3`?
  88b1873: test rax,rax ; je ...(skip)   ; sentinel-3 nil is skipped; a raw-null 0 is NOT
  88b187c: mov [rsp+0x7f0],rax ; mov rax,r12 ; and $-8,r12   ; untag element
  88b188b: test r12,r12 ; jne 88b1a11    ; if non-null read field...
           ...build "field access on nil receiver"; call rt_eprintln_str...
  88b1a0f: ud2                            ; <-- FAULT RIP (render_commands+0x3a0), the compiler
  88b1a11: mov (%r12),%r14                ; nil-field-guard: element untags to 0, `command.kind` read
```
`command.?` lowers to `rt_native_neq(command, 3)` (boxed-nil **sentinel 3**), but the actual
element value is **0** (raw null). `0 != 3` ⇒ `.?` reports "present" ⇒ the `if command.? == false`
skip at `draw_ir_adv.spl:491` is bypassed ⇒ `val command_kind = command.kind` (offset-0 read) on a
null ⇒ nil-field-guard `ud2`. (Same 0-vs-3 split the interpreter already has: interp treats 0 as
absent; freestanding `.?` only tests sentinel 3.)

### Where the null comes from (producer-side, Simple-level)
`src/lib/common/ui/window_scene_draw_ir.spl` builds the **embedded window batch** (`_wm_draw_ir_window_batch`,
lines 660-676) as a `[DrawIrCommand]` array literal that MIXES annotated `draw_ir_rect(...)`
(`-> DrawIrCommand`) with THREE producers that had **no return-type annotation**:
`_wm_draw_ir_window_box` (450), `_wm_draw_ir_text` (470), and their helper `_wm_draw_ir_window_style`
(442). Per this file's own documented failure mode ("native inference has historically treated an
unannotated field/return projection as a generic runtime value", draw_ir_adv.spl:570-572), under
`--entry-closure --target x86_64-unknown-none --opt aggressive` the erased returns are (best
explanation) boxed/erased and stored into the typed `[DrawIrCommand]` slots as values that untag to 0.
PROVEN from disasm: the element untags to 0 and `.?` tests only sentinel 3. INFERRED: the ANY-erasure
byte path (raw element value was not printed) — but the mechanism is confirmed *load-bearing* by the
annotate/de-annotate delta (adding the 3 return types is the sole change that makes the fault vanish).
**Element[0] of that batch is `_wm_draw_ir_window_box(...,"shadow",...)`** — the first-accessed command
— which is exactly where the fault fires. This batch is the one that triggers the 8 MB offscreen surface (surface_id set),
matching the fault landing right after the `[heap] alloc sz=0x800020` bursts.

### Fix (pure-Simple, root, matches this codebase's documented remedy)
`window_scene_draw_ir.spl`: added explicit return types to the three producers:
`_wm_draw_ir_window_style(...) -> [DrawIrStyleProp]`, `_wm_draw_ir_window_box(...) -> DrawIrCommand`,
`_wm_draw_ir_text(...) -> DrawIrCommand`. This gives each producer a concrete typed return so the
array literal has homogeneous `DrawIrCommand` elements (no ANY-erasure). No guard band-aid, no
compiler change — the source of the nil is removed. (Seed defect worth filing separately: `.?`
lowering should treat untagged==0 as absent, not only sentinel 3.)

### Boot result (fresh clean build, md5 13b267a8, `build/os/_wklast/`, current seed, NVMe, vfs skip kept)
- **render_commands+0x3a0 nil-command fault ELIMINATED — ZERO faults, zero `EXCEPTION FRAME`s.**
  (The two `[fault]` serial lines are handler *setup* logs `_fault_handler patched`, not faults.)
- The render now progresses PAST the previously-faulting batch: 12 × 8 MB offscreen allocs vs the
  baseline's 9 (baseline faulted at the 1st embedded batch's element[0]; the wall was masked).
- **NEW, DISTINCT downstream blocker: `[PANIC] heap exhausted`** (`heap_off=0xbfffff0 req=0x20
  limit=0xc000000` = 192 MB). Repeated per-embedded-batch 8 MB `Engine2D.create_offscreen`
  (`draw_ir_adv.spl:647`, caller 0x8010776) on a heap whose `[heap] alloc off_before/off_after`
  advance monotonically (INFERRED bump allocator: `offscreen.shutdown()` at line 666 evidently does
  not reclaim — offsets never decrease), so ~24×8 MB exhausts 192 MB before first-frame completes.
  This is a SEPARATE pre-existing defect the nil-fault was masking; my 3 return annotations cannot
  change offscreen-allocation logic. `first-frame-rendered` NOT reached; screendump 3840x1092 still
  25.01% non-black (1048576 px, a pre-completion capture identical to baseline).
- **Verdict: assigned "last fault" FIXED (zero faults). Zero-fault-first-frame now blocked by the
  offscreen-surface-vs-192MB-bump-heap exhaustion — recommend that as the next lane** (options:
  reclaim/pool offscreen surfaces on baremetal, or prefer the direct translate+clip path — lines
  618-620 `use_embedded_surface` gate — for the software/baremetal backend so no 8 MB surface is
  allocated; both need their own boot validation).

Changed file: `src/lib/common/ui/window_scene_draw_ir.spl` (3 return-type annotations; backed up
`scratchpad/lastfault_backup/window_scene_draw_ir.spl.{PREFIX,FIX}`). Evidence:
`build/os/_wklast/{serial.log,screendump.ppm,build.log}` (also copied to `scratchpad/lastfault_backup/`),
disasm `scratchpad/rc_disasm64.txt`, symbols `scratchpad/nm_all.txt`.
