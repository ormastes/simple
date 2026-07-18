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
- **Status:** OPEN — root cause isolated 2026-07-07 (see "Root cause
  (isolated)" below: two stackable seed-codegen defects B1+B2; the old
  "store-side `>>3`" theory is WRONG — the store is correct, the corruption is
  on the read/fstring-display side). Fix is Rust-seed, gated on
  `--full-bootstrap --deploy`. Worked around in
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

## Root cause (isolated 2026-07-07)

Live-reproduced with a minimal 6-line probe (real headless QEMU boot) and
confirmed by `llvm-objdump`/`nm`/disassembly. It decomposes into **two
independent, stackable seed defects, plus one stale lead now resolved.** The
old "store-side `>>3` untag" theory above is WRONG: disassembly shows the
store is a bare `movq $0x400, (%r9)` (raw 1024, correct for a primitive slot)
— the corruption is entirely on the **read/fstring-display** side.

### B0 — STALE LEAD, already fixed (do not re-investigate)

The 05-28 memory's "missing module-init calls in freestanding" is resolved in
current source: `native_project/linker.rs:255-256` now gates the Mach-O
underscore-strip on `effective_target().os` (the target), not host OS;
`linker.rs:649-828` generates a real `__simple_call_module_inits`; and
`arch/x86_64/boot/crt0.s:301-311` calls it before `spl_start` (line 320). This
machinery only covers **heap-backed** global initializers
(`common_backend.rs:1630-1648`); a `var g_probe: i32 = 236` initializer is a
plain compile-time constant baked by `declare_globals`
(`common_backend.rs:1209-1238`), so B0 is unrelated to this bug.

### B1 — non-zero primitive `var` globals land inside `.text`, not `.data`/`.bss`

Confirmed via `llvm-objdump -h`: `.text` = `0x100000..0x159658`, `.data` at
`0x168000`, `.bss` at `0x169000`; `nm` puts `g_probe` at **`0x159650`** — 8
bytes inside `.text`. Explains the deterministic uninitialized-garbage read
(the slot overlaps nearby code bytes — hence the byte-identical garbage
constant across two independent repro files). By itself this does NOT cause
the `>>3` corruption (the slot is still RW-mapped and addressed correctly by
VMA). This is the same defect independently noted as "root cause A" in
`project_simpleos_gui_boot_2026-05-28`, still present.

### B2 — the actual `>>3` mechanism: unboxed value handed to a tag-ambiguous runtime fn

Disassembly of `_bump_probe` shows `movq (%rsi), %rdi` (raw 8-byte load of the
slot) then a direct `call rt_value_to_string` with **no `ishl …, 3`** between
— i.e. `MirInst::BoxInt` was never emitted for this argument. Chain:
1. `hir/lower/expr/literals.rs:230-249` (`lower_fstring`) emits
   `BuiltinCall{name:"rt_value_to_string", args:[g_probe ref]}`.
2. `mir/lower/lowering_expr_builtin.rs:120-190` boxes the arg only when
   `arg.ty` is a primitive int (`I8..U64` → `BoxInt`, line 165-172); anything
   else (notably `TypeId::ANY`) passes through **unboxed**.
3. `codegen/instr/mod.rs:1305-1341` emits `ishl val,3` only if `BoxInt` is
   present — it was absent, so `arg.ty` for the `g_probe` ref resolved to
   **non-primitive** (inferred `TypeId::ANY`: the observed `movq`/8-byte load
   width matches `type_id_to_cranelift(ANY)==I64`, `types_util.rs:26-46`; a
   genuine `I32` would `movl`).
4. `arch/x86_64/boot/baremetal_stubs.c:907-925` (`rt_value_to_string`)
   disambiguates boxed-vs-raw by `IS_INT(v) = (v & 0x7) == 0`
   (`baremetal_runtime.h:39-54`) — so **any raw untagged multiple of 8**
   (1024, 768) is bit-identical to a `BoxInt`-tagged small int (`TAG_INT==0`)
   and is wrongly `DECODE_INT`'d as `v>>3` instead of hitting the raw-value
   fallback. This is exactly why only multiples of 8 corrupt.

**Open question (not resolvable read-only):** *why* an explicitly-typed
`var g_probe: i32` reference resolves to `ANY` at this call site under the
`native-build` pipeline. Three hypotheses were traced and **ruled out** (dead
ends — don't recheck): single-pass/declaration-order lowering
(`module_pass.rs` is genuinely two-pass); `TypeRegistry::default()` vs
`::new()` (all `Lowerer` ctors seed `"i32"->I32`); and
`SIMPLE_ALLOW_FREESTANDING_STUBS` gating an alternate MIR path (that env var is
link-time only). Note: the identical snippet prints correctly under both the
interpreter and the Cranelift JIT (`pipeline/execution.rs`) — only the
`native_project/compiler.rs` lowering path is affected. `--emit-hir/--emit-mir`
are not wired into `native-build`'s arg parser, so the exact upstream defect
needs a one-line diagnostic probe (see "Suggested fix direction").

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

## Suggested fix direction (seed-gated — not implemented here)

Fix locus is the **Rust seed** for both B1 and B2 → requires
`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy`
(incremental bootstrap won't pick up a seed codegen/HIR change). A
`baremetal_stubs.c`-only defense (B2 option 2 below) is the exception — it is
relinked by any `native-build` without touching the seed/bootstrap.

- **Step 0 (diagnostic, ~2 min with seed write access):** add a gated
  `eprintln!` of `arg.ty` in `mir/lower/lowering_expr_builtin.rs` right after
  line 122, guarded on `name == "rt_value_to_string"`; rebuild only the seed
  (`cargo build` in `src/compiler_rust`, no full bootstrap needed to iterate);
  re-run the 6-line probe from "Repro". Confirms whether `arg.ty` is `ANY` (as
  inferred) or something else, before touching real logic.
- **Fix B1 (`.text` placement):** ensure non-zero writable primitive-global
  data lands in a section the linker script's `.data`/`.bss` rules catch
  (cranelift-object section naming for `Preemptible`+writable+non-zero data,
  or the ELF32-wrap/link step in `native_project/{compiler.rs,linker.rs}` /
  `codegen/common_backend.rs`). Expected: `initial g_probe=236` (no garbage).
- **Fix B2 (`>>3` corruption), root fix:** make `arg.ty` resolve to the
  declared primitive (`I32`) at the boxing-gate call site — the existing
  `needs_boxing` gate (`lowering_expr_builtin.rs:139-149`) then does the right
  thing, no new logic. Expected: `after-assign g_probe=1024` (not 128).
- **Fix B2, defense-in-depth (C, no bootstrap):** `rt_value_to_string`'s
  `IS_INT`-first heuristic is unsound (raw multiple-of-8 collides with a
  tagged small int); after the root fix guarantees boxing for this call,
  consider removing the raw fallback / using a non-tag signal.
- Full verification: rerun the isolated probe, then
  `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`; consider
  converting `gui_entry_engine2d.spl`'s local-`val` workaround back to a
  module `var` as a regression guard once fixed. Then mark this bug CLOSED and
  correct `project_simpleos_gui_boot_2026-05-28`'s "UNFIXED root cause B"
  (superseded by B0 above).
