# Bug: Cranelift freestanding wrapper-profile build corrupts nonzero module-level `var` global i32 (reads back value >> 3)

- **ID:** freestanding_wrapper_profile_i32_global_var_shifted_2026-07-02
- **Severity:** P2 (silent: any `var X: i32 = <nonzero>` module-level global
  used by a `_uses_baremetal_wrapper_profile` freestanding target — e.g.
  `gui_entry_engine2d.spl` — reads back corrupted; workaround exists so not
  release-blocking, but any future feature that stores non-boolean/non-zero
  state in a module `var` on this profile will silently miscompute)
- **Backend:** Cranelift, `native-build --entry-closure` freestanding
  wrapper profile (`os.qemu_runner._uses_baremetal_wrapper_profile` /
  `_needs_freestanding_stub_env`; reproduced on the `wm-simple-web` x86_64
  QEMU target, `--target x86_64-unknown-none`, host macOS aarch64 building
  x86_64)
- **Status:** OPEN — worked around in
  `examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl` by not
  using module-level `var` globals for the new WM fullscreen/restore state;
  state is threaded through locals and function parameters instead (which
  read/write correctly in this profile).

## Symptom

Added a module-level global to `gui_entry_engine2d.spl`:

```
var g_win0_w: i32 = 236
```

and, inside a function, assigned a plain literal:

```
fn _wm_window0_enter_fullscreen():
    g_win0_w = 1024
    serial_println("[debug] g_win0_w={g_win0_w}")
```

Boot serial log:

```
[debug] initial g_win0_w=-4369124742942603179   # garbage before any assignment
...
[debug] g_win0_w=128                             # after "g_win0_w = 1024" — should be 1024
```

`1024 >> 3 == 128` exactly (also reproduced with `768 -> 96`). The same
corruption happens whether the RHS is a literal, a local `val`, or a function
call return value — the bug is in the STORE (and/or the interpolated READ) of
the global slot itself, not in evaluating the RHS expression. A local
`val fb_w_now: i32 = _fb_w()` and its interpolation both read back correctly
(`1024`) — only the module-level global is affected.

The *initial* (never-assigned) value is also not the declared initializer
(`236`) — it is 64-bit garbage, consistent with the previously-documented
"module globals placed in text region, uninitialized" class of bug for this
freestanding profile (see `project_simpleos_gui_boot_2026-05-28` in
project memory / `doc/09_report/`).

## Root cause (not yet isolated)

Not investigated to completion (out of scope for the WM-fullscreen feature
this was found under). Working theory: the freestanding wrapper-profile
Cranelift lowering for module-level primitive globals routes through the
same value-representation path used for heap/boxed values elsewhere in the
codebase (tagged pointers, `value >> 3` to strip a 3-bit tag), and
mistakenly applies the untag shift to a plain immediate/stack value being
stored into a **primitive, non-heap** global slot. This would explain both
symptoms: the uninitialized-garbage read (the module-init writer for
primitive globals is not run in this profile, matching the known
`__module_init` gap for heap globals) and the exact `>>3` corruption on
write-back.

## Repro

1. In any `_uses_baremetal_wrapper_profile` freestanding entry (e.g.
   `examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl`), add
   `var g_probe: i32 = 0` and, in a function invoked at boot, do
   `g_probe = 1024; serial_println("g_probe={g_probe}")`.
2. Build:
   ```
   SIMPLE_BOOTSTRAP=1 SIMPLE_LIB="$(pwd)/src" SIMPLE_OS_LOG_MODE=off \
     SIMPLE_ALLOW_FREESTANDING_STUBS=1 PATH="/opt/homebrew/opt/llvm/bin:$PATH" \
     bin/simple native-build \
       --source build/os/generated --source src/os --source src/lib \
       --source examples/09_embedded/simple_os/arch/x86_64 \
       --backend cranelift --cpu x86-64-v1 --opt-level=aggressive --log off \
       --entry-closure --entry examples/09_embedded/simple_os/arch/x86_64/gui_entry_engine2d.spl \
       --target x86_64-unknown-none -o build/os/simpleos_wm_simple_web_check_32.elf \
       --linker-script examples/09_embedded/simple_os/arch/x86_64/linker.ld
   ```
3. Boot headless and read the serial log:
   ```
   qemu-system-x86_64 -no-user-config -monitor none -net none \
     -machine q35 -cpu qemu64 -m 2G -serial file:/tmp/serial.log \
     -display none -no-reboot -kernel build/os/simpleos_wm_simple_web_check_32.elf -vga std
   ```
4. `strings /tmp/serial.log | grep g_probe` shows `128`, not `1024`.

## Workaround applied

`gui_entry_engine2d.spl`'s WM fullscreen/restore feature stores window-0
geometry entirely via local `val`/function parameters (`win0_fullscreen:
u64` passed into `_present_mdi_scene_direct_fb`, `fs_w`/`fs_h` locals in
`spl_start`) instead of module-level `var` globals. This reads/writes
correctly and was verified end-to-end via
`scripts/check/check-simpleos-wm-fullscreen-evidence.shs` (real QEMU boot +
QMP `pmemsave` screendumps, fullscreen marker size == 1024x768, nonzero
pixel delta between maximized and restored captures).

## Suggested fix direction (not implemented here)

- Compare the freestanding-profile Cranelift lowering for a primitive
  (`i32`/`u64`) module global's store instruction against the normal
  (non-freestanding) lowering to find where a `>>3` (or `<<3` on write —
  needs a debugger/objdump pass to say which side) tag-shift is being
  applied to a value that was never tagged.
- Cross-check against the existing heap-global `__module_init` gap
  (`llvm_backend_missing_module_init_heap_globals_2026-06-15`,
  `native_object_cache_key_omits_seed_version_2026-06-15`) — this may be the
  Cranelift-side counterpart of the same "freestanding profile doesn't run
  global initializers" gap, but the `>>3` value corruption on top of that is
  a distinct symptom worth isolating on its own.
