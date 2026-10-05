# JIT: `&mut local` passed to an extern out-param sends the value, not the address; main_gui could not open a window

- **Filed:** 2026-10-05
- **Area:** `src/compiler_rust/compiler/src/codegen/instr/pointers.rs`
  (`compile_pointer_ref`) × `src/lib/nogc_sync_mut/sffi/dynamic.spl`
  (`_sffi_dlopen_checked`) × `src/lib/nogc_sync_mut/ui/gui_renderer.spl`
- **Status:** main_gui unblocked 2026-10-05; seed root cause FIXED 2026-10-05
  (see "Seed fix")

## Symptom

```
SIMPLE_SHOWCASE_W=3840 SIMPLE_SHOWCASE_H=2160 <seed> run src/app/ui_showcase/hosts/main_gui.spl
GuiRenderer: cannot load build/sffi/libspl_winit.<dylib|so|dll> — build it with ...
showcase gui: no window (missing display or build/sffi/libspl_winit)
```

This printed although the dylib was present and valid, and also with
`SIMPLE_SPL_WINIT_PATH` set. The override was honoured; the message hid the
real error.

## Three stacked causes

1. **JIT out-param (root).** For `spl_dlopen_checked(path, &mut handle)`,
   MIR emits `PointerRef { Borrow, source: <loaded value> }`, and Cranelift's
   `compile_pointer_ref` passes the source value through unchanged. The
   provider therefore received `out_handle = 0` (null) and returned status 1
   (invalid argument) before ever calling `dlopen`. The same program run in
   the interpreter loads the library. Every `&mut scalar` extern out-param is
   affected under the JIT, for example `spl_wffi_call_bool1_checked(...,
   &mut released)` in `gui_renderer.spl`.
2. **Stale provider.** The shared `build/sffi/libspl_winit.dylib` (2026-09-17)
   lacks `rt_winit_window_poll_event` and `rt_winit_event_loop_window_count`,
   both of which the facade now requires.
3. **macOS main thread.** winit needs `SIMPLE_GUI=1` so that it runs on the
   main thread. Without it the event loop panics, and that is now reported.

## Fix in this change (Simple side)

- `_sffi_dlopen_checked`:
  - Status 1 for a non-empty path is the out-slot transport rejection. It now takes the existing direct-return fallback (`spl_dlopen`), the same path already used for the interpreter's writeback-loss case.
  - Status 2 and a failed direct load now explain themselves: "returned null: wrong architecture, missing dependency, or not a shared library".
- `GuiRenderer.create`:
  - Prints every candidate path's load error.
  - The incomplete-ABI message names the missing `rt_winit_*` symbols.
- `main_gui`: the "no window" line points to the `GuiRenderer:` cause line instead of guessing.

## Seed fix (2026-10-05)

- MIR (`mark_extern_scalar_out_slots`, `lowering_expr_call.rs`): for a call
  to an `extern fn`, a `&mut <scalar local>` argument's `PointerRef` is marked
  `RawMut`. Before this, MIR never emitted RawMut. A `&mut [u8]` argument is a
  collection handle and stays by-value.
- Codegen (`pointers.rs`): a RawMut `PointerRef` of a loaded local stores the
  current value in an 8-byte stack slot and passes the slot's address.
  `writeback_extern_out_slots` runs after the call; it loads the slot back
  into the local's Variable.
- Tests: `src/compiler_rust/compiler/tests/extern_out_slot_jit.rs` (2/2).
  - The repro `spl_wffi_try_call_i64_out(0, [], 0, &mut probe)` must zero
    `probe` and answer status 2.
  - The generalization covers two out locals written inside a loop and branch.
  - With the MIR marking disabled, the repro test fails: its process dies
    instead of reporting status 2.

The Simple-side direct-return fallback in `_sffi_dlopen_checked` stays as a
belt-and-braces path for the interpreter's historical writeback loss.

## Evidence

- `winit_probe` (plain `main`, JIT):
  - before: `E-SFFI-001: failed to load provider: build/sffi/libspl_winit.dylib (status 1)`
  - after: `loaded ok`
  - The interpreter loaded it both before and after.
- With the rebuilt provider (`sh scripts/build/build_spl_winit.shs`),
  `SIMPLE_GUI=1 SIMPLE_SHOWCASE_W=3840 SIMPLE_SHOWCASE_H=2160
  SIMPLE_SHOWCASE_FRAMES=3 <seed> run src/app/ui_showcase/hosts/main_gui.spl`
  printed `showcase host=gui frames=3`.
- The stale provider now reports
  `missing: rt_winit_window_poll_event, rt_winit_event_loop_window_count`.
- `test/01_unit/lib/nogc_sync_mut/sffi/dynlib_load_checked_spec.spl` (3/3):
  - Under `run`, the "present non-library" case fails on the old loader and passes on the new one.
  - The soname case passed on both.
