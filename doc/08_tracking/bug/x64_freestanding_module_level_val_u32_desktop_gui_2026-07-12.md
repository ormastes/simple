# BUG: freestanding native-build silently corrupts a module-level `val: u32` read inside `spl_start()` (desktop GUI entry)

**Status:** open
**Severity:** medium (silent corruption, not a crash -- easy to miss; blocks refactoring magic-number literals into named constants for baremetal entry files)
**Component:** native-build freestanding codegen (`--target x86_64-unknown-none --backend cranelift`), `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`
**Found:** 2026-07-12, while making the SimpleOS desktop GUI scanout resolution a named constant instead of a literal

## Symptom

`gui_entry_desktop.spl` originally hardcoded the desktop's BGA scanout resolution as two `u32` literals local to `spl_start()`:

```simple
fn spl_start():
    val framebuffer_width: u32 = 3840
    val framebuffer_height: u32 = 2160
    ...
    val scanout = bga_init_scanout(framebuffer_width, framebuffer_height, framebuffer_bpp)
```

This boots correctly end-to-end (verified via `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`): the guest's `[scanout-evidence]` serial marker reports `width=3840 height=2160`.

Hoisting the same two values to **module-level** `val` constants and referencing them from `spl_start()`:

```simple
val DESKTOP_FB_WIDTH_4K: u32 = 3840
val DESKTOP_FB_HEIGHT_4K: u32 = 2160

fn spl_start():
    val framebuffer_width: u32 = DESKTOP_FB_WIDTH_4K
    val framebuffer_height: u32 = DESKTOP_FB_HEIGHT_4K
    ...
```

compiles and boots without error, but the guest's `[scanout-evidence]` marker now reports **garbage**: `width=16000 height=1048` (stride=64000, consistent with width but not with any real display mode -- and not simply a scaled/rounded value of 3840x2160). The BGA readback path itself (`bga_init.spl:bga_init_framebuffer`) is unchanged and known-good, so the corruption happens before/at the point `framebuffer_width`/`framebuffer_height` reach the call to `bga_init_scanout`.

An intermediate variant tried a `fn desktop_fb_width() -> u32: ... DESKTOP_FB_WIDTH_4K` wrapper plus a `text`-typed `DESKTOP_FB_MODE` mode switch (`if DESKTOP_FB_MODE == "8k": ...`) -- same garbage result (`width=16000 height=1048`), ruling out the function-call indirection or the text comparison as the sole cause; the plain module-level `val: u32` read alone reproduces it.

## Reproduction

1. In `examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl`, add near the top (after the `use` block, before `spl_start`):
   ```simple
   val DESKTOP_FB_WIDTH_4K: u32 = 3840
   val DESKTOP_FB_HEIGHT_4K: u32 = 2160
   ```
2. In `spl_start()`, change the two local `val` initializers to reference the module-level constants instead of the literals.
3. Build: `SIMPLE_BOOTSTRAP=1 SIMPLE_LIB=$PWD/src SIMPLE_OS_LOG_MODE=off SIMPLE_ALLOW_FREESTANDING_STUBS=1 <simple> native-build --source build/os/generated --source examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl --backend cranelift --cpu x86-64-v1 --opt-level=aggressive --log off --mode dynload --entry-closure --entry examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl --target x86_64-unknown-none -o <out>.elf --linker-script examples/09_embedded/simple_os/arch/x86_64/linker.ld` (or just run `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`, which does this).
4. Boot under QEMU and check the `[scanout-evidence]` serial marker -- width/height are garbage instead of 3840/2160.

## Workaround in place

Reverted to the original plain `u32` literals local to `spl_start()`; resolution/DPI/mode intent is documented in a comment instead of hoisted to a module-level constant. See `gui_entry_desktop.spl:spl_start()`.

## Suspected relation

Possibly the same class of freestanding layout/init-order sensitivity as `doc/08_tracking/bug/x64_freestanding_layout_sensitive_dup_displaced_stores.md` and `doc/08_tracking/bug/x64_freestanding_mmio_read_u8_address_dependent_zero.md` -- module-level global initializers on this freestanding target have a history of being layout- or init-order-sensitive. Not confirmed; no root cause identified yet, only the reproduction above.

## Update 2026-07-17 — likely a DIFFERENT root cause than the sibling module-init bugs; not fixed by this pass

This bug doc was grouped with
`doc/08_tracking/bug/freestanding_entry_module_val_initializers_never_run_2026-07-06.md`
and `doc/08_tracking/bug/baremetal_entry_closure_class_instantiation_fault_2026-07-06.md`
under the hypothesis that all three share the "no `__module_init_*`
emission/aggregation" root cause. Host-side testing this pass shows that
hypothesis does NOT hold for this specific bug:

- `DESKTOP_FB_WIDTH_4K: u32 = 3840` is a bare integer literal --
  const-foldable by `lower_const_expr`
  (`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:3026`).
- Reproduced the equivalent shape on the plain HOST hosted target
  (`val MARKER: i64 = 42; fn main() -> i64: return MARKER`, native-build, no
  `--entry-closure`, no freestanding target) and it returns the correct value
  (`42`) every time -- the const-fold path works correctly when it applies.
- By contrast, the module_init aggregator work landed this pass (see the
  other two docs' 2026-07-17 updates) is about NON-foldable initializers
  (calls, binops, cross-module reads), which this bug's literal is not.

So this bug's corruption (`width=16000 height=1048` instead of `3840x2160`)
most likely comes from something freestanding-target-specific -- section
placement, relocation handling, or an init-order/layout sensitivity as the
original "Suspected relation" section already guessed -- rather than the
"initializer never runs" gap. **Not fixed, not further root-caused, and not
verified this pass**: reproducing/diagnosing it requires an actual
freestanding x86_64-unknown-none build + boot (or at minimum an objdump/relocation
inspection of a real freestanding artifact with this shape), which is out of
scope here (no rebuild, no QEMU/board boot per this pass's constraints).
Left open; do not close this doc from the module-init link-stage fix landed
in the other two docs.
