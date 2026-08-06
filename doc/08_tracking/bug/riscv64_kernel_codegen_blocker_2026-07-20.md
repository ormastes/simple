# Bug: RISC-V 64 full-kernel boot path fails rv64 codegen (interrupt.spl + privilege_bridge.spl)

**ID:** riscv64-kernel-codegen-blocker-2026-07-20
**Domain:** compiler/backend (rv64 MIR + codegen), os/simpleos
**Severity:** blocker (for the rv64 boot→login→ls→launch goal)
**Filed:** 2026-07-20

## Summary

The rv64 serial management shell (`login`/`ls`/`launch`) is implemented,
committed, and reachable on the boot path
(`entry.spl → kernel_main → Riscv64Boot.boot_main → os_main() → serial_shell_main`,
boot.spl:79-80). But the **full-kernel entry** (`examples/09_embedded/simple_os/arch/riscv64/entry.spl`)
fails to compile to a bootable rv64 ELF due to two pre-existing rv64 codegen
gaps in modules the full boot path transitively imports. The only rv64 entry
that *does* build (`smoke_entry.spl` / `fpga_serial_entry.spl`) uses
`rt_riscv_*` extern stubs and never reaches `boot_main`/`os_main`/`serial_shell_main`,
so it cannot exercise the interactive shell. Net: rv64 boot→login→ls→launch is
unverifiable until the rv64 codegen lowers the two constructs below.

## Evidence (build log, `bin/simple native-build --entry .../entry.spl --target riscv64-unknown-none`)

```
FAILED FILES (2):
  - src/os/kernel/arch/riscv64/interrupt.spl
      => mir: Unsupported HIR construct: complex lvalue: Deref(HirExpr { kind: Local(1), ty: TypeId(1761) })
  - src/os/kernel/privilege/privilege_bridge.spl
      => codegen: Module error: 1 function body/bodies failed to compile: [bridge_has_mirror]
         set SIMPLE_ALLOW_STUB_FALLBACK to emit empty stubs instead (unsafe — binary will silently misbehave)
Build failed: native-build aborted: 2 file(s) failed to compile
```

Also seen (non-fatal but indicative of weak rv64 module resolution):
`cannot resolve import: module path segment 'std' not found` (checked path
`src/os/crypto/std`) and `[DEBUG lower_lvalue] Unsupported lvalue kind: Deref(...)`.

## Root cause (two distinct gaps)

1. **Complex deref lvalue in MIR lowering** — `interrupt.spl` (and likely
   others) produce a `Deref(Local)` lvalue the rv64 cranelift path cannot lower.
   Same class as prior baremetal lowering gaps.
2. **`bridge_has_mirror` codegen failure** — `privilege_bridge.spl` function
   body fails codegen; the offered `SIMPLE_ALLOW_STUB_FALLBACK` escape hatch is
   explicitly unsafe ("binary will silently misbehave") and is NOT acceptable
   per the no-shortcut rule — the function must actually compile.

## Impact

- rv64 boot→login→ls→launch cannot be built/booted. The stub-based
  `smoke_entry` builds (22 KB) but is a probe, not the shell path, and its
  freestanding link also reports "2 unexpected unresolved symbol(s)".
- The serial shell source itself is correct and on the intended path; the
  blocker is purely the rv64 codegen's inability to compile the full kernel
  dependency closure.

## NOT a workaround

`SIMPLE_ALLOW_STUB_FALLBACK=1` would let it link but silently misbehave —
forbidden (no shortcuts). The fix is to make rv64 codegen lower (1) complex
deref lvalues and (2) `bridge_has_mirror`, or to refactor those two modules
to avoid the unsupported constructs.

## Related

- rv64 serial shell + login + ls: commit 6b87d996bf62
- rv64+rv32 launch command: commits cc5256812d48 / 8ef6c4c8a11a
- rv32 emission blocker: doc/08_tracking/bug/riscv32_cranelift_emission_blocker_2026-07-20.md
- Bidirectional serial harness (ready, pending a bootable ELF):
  scripts/qemu/check_simpleos_rv64_serial_shell.shs

## Update 2026-08-06: still blocked, gap moved further down the closure

Re-tried while pushing the riscv64 toolchain-payload boot campaign forward
(cross-built `bin/release/riscv64-unknown-simpleos/simple` userland payload
landed today, never booted — see
`doc/03_plan/os/simpleos/in_guest_simple_toolchain_multiarch_plan.md`). Built
directly with the Rust seed (mirroring the x86_64 UEFI harness pattern,
bypassing the `bin/simple os build` scenario runner — see the separate
harness-probe-timeout note below):

```
SIMPLE_BOOTSTRAP=1 SIMPLE_LIB="$(pwd)/src" src/compiler_rust/target/release/simple \
  native-build --source build/os/generated --source src/os --source src/lib \
  --backend cranelift --entry-closure \
  --entry src/os/kernel/arch/riscv64/boot.spl \
  --target riscv64-unknown-none -o build/os/simpleos_riscv64.elf \
  --linker-script src/os/kernel/arch/riscv64/linker.ld
```

The two 2026-07-20 blockers (`interrupt.spl` Deref lvalue,
`privilege_bridge.spl` `bridge_has_mirror`) are **not** what stops the build
now — the closure gets further before failing on a different file/symbol:

```
FAILED FILES (1):
  - src/os/kernel/ipc/cspace_spawn.spl => codegen: Module error: codegen:
    1 function body/bodies failed to compile: [SingleUseLedger.is_armed];
    set SIMPLE_ALLOW_STUB_FALLBACK to emit empty stubs instead (unsafe —
    binary will silently misbehave)
```

Root cause is visible earlier in the log:
`[CODEGEN-STUB-FALLBACK] body compilation failed for 'SingleUseLedger.is_armed':
ModuleError("... Unsupported feature: should be implemented in ISLE: inst =
\`v63 = vany_true.i64x2 v62\`, type = \`Some(types::I8)\`")` — the cranelift
rv64 backend has no ISLE lowering for a 128-bit `vany_true` vector-any-true
reduction. Same "not a workaround" rule applies: `SIMPLE_ALLOW_STUB_FALLBACK`
is explicitly unsafe and was not used. Net: rv64 full-kernel boot (and
therefore booting the cross-built toolchain payload) is still blocked purely
in the compiler backend — a real ISLE lowering gap for `vany_true.i64x2`, not
a riscv64-silicon or QEMU/OpenSBI issue.

## FIXED 2026-08-06: was compiler overgeneration, not a genuine ISLE gap

Investigated whether to add a riscv64 ISLE lowering rule for `vany_true.i64x2`.
It is not possible/appropriate: `src/compiler_rust/vendor/cranelift-codegen/src/isa/riscv64/lower.isle`
already has a general `vany_true` rule (line 2778), gated by `(ty_supported_vec
ty)`. `ty_supported_vec` (`src/compiler_rust/vendor/cranelift-codegen/src/isa/riscv64/lower/isle.rs:185`)
requires `ty_vec_fits_in_register`, which requires `ty.bits() <=
min_vec_reg_size()` — and `min_vec_reg_size()` is `0` on a bare riscv64 target
with no `V` extension. So **no** vector type, of any lane width, can ever match
that rule on this target: there is no vector register file to lower onto, and
adding an i64x2-specific ISLE rule would be lowering vectors onto hardware that
doesn't exist.

The actual root cause: `src/compiler_rust/compiler/src/codegen/instr/calls.rs`
hand-inlines two numeric intrinsics — `compile_inline_numeric_contains_u64`
(`rt_numeric_contains_u64[_data]`, called for `SingleUseLedger.is_armed`'s
`token_ids[i] == token_id` scan) and `compile_inline_numeric_xor_sum_u64`
(`rt_numeric_xor_sum_u64[_data]`) — and both **unconditionally** emitted
explicit `I64X2` SIMD (`splat`/`load.i64x2`/`bxor`/`vany_true`) with no check of
what the target ISA actually supports. This is MIR/codegen overgeneration, not
a lowering gap: any 2-lane u64 SIMD-any-true/reduce for a scalar array-of-u64
should scalarize on a target with no vector unit.

**Fix landed:** both functions now check
`ctx.module.isa().triple().architecture` and only take the I64X2 SIMD fast path
on `X86_64` (SSE2 baseline) / `Aarch64` (NEON baseline), which are guaranteed
to have real hardware support. Every other target (riscv64 without `V`,
`s390x`, `pulley`, etc.) falls back to a plain scalar per-element loop — for
`contains_u64` this reuses the existing tail-loop scalar body already present
for the "remainder" case; for `xor_sum_u64` a new
`compile_scalar_numeric_xor_sum_u64` helper mirrors the header/bounds-check
dance and applies the same `raw_data ? sum : sum << 3` result transform the
SIMD path used. x86_64/aarch64 codegen is byte-for-byte unchanged (same
instruction order under `use_simd == true`).

**Verified:** rebuilt the Rust seed and re-ran the exact riscv64 full-kernel
build command from the 2026-08-06 update above. Before the fix: `FAILED FILES
(1): cspace_spawn.spl => ... SingleUseLedger.is_armed ... vany_true.i64x2 ...
should be implemented in ISLE`. After the fix: **0 FAILED FILES** — every
`.spl` in the closure, including `cspace_spawn.spl`, now compiles and the build
reaches the link stage. Sabotage-tested: reverted `calls.rs` to the pre-fix
version, rebuilt, reran the identical command — the exact original
`SingleUseLedger.is_armed` / `vany_true.i64x2` "should be implemented in ISLE"
failure reproduced verbatim, then the fix was restored and re-verified.

**New blocker exposed further down (not fixed here, out of this task's scope):**
the build now fails at the **C inline-asm assembly stage**, not compile:
```
Build failed: compile inline asm C failed: .../simple_asm_blocks.c:445:12:
error: unrecognized instruction mnemonic, did you mean: c.li, c.lui, li, lui?
  "cli\n.Lhalt_loop:\nhlt\njmp .Lhalt_loop\n"
```
Pinned to `src/os/kernel/interrupts/idt.spl:230-235`, function `_halt()`:
```
fn _halt():
    """Disable interrupts and halt CPU forever."""
    asm """
        cli
        .Lhalt_loop:
        hlt
        jmp .Lhalt_loop
    """
```
`cli`/`hlt`/`jmp` are x86_64-only instructions with no riscv64 equivalent
mnemonics — this inline asm block is unconditionally compiled regardless of
target, meaning `idt.spl` (or something that imports it) is reachable from the
riscv64 boot entry-closure despite being x86_64-specific. This needs either
target-gating the `_halt()` asm block (per-arch halt implementations, mirroring
how `x86_64/cpu.spl` / `x86_32/cpu.spl` already have their own `hlt`/`x86_hlt`)
or fixing the import chain so riscv64 doesn't pull in this x86_64-only IDT
module at all. Left undone here as a distinct, unrelated bug class (bad-target
inline asm reachability, not compiler backend codegen) — filing as a new
tracked item is the next step rather than forcing a fix into this task.

## FIXED 2026-08-06: `_halt()` target-gated via existing `rt_*` extern idiom

Fixed by reusing an idiom already live in this exact file: `idt.spl` already
declares `extern fn rt_lidt(...)` / `extern fn rt_read_cr2()` and calls into
`src/runtime/startup/baremetal/runtime_minimal.c`, which implements each
`rt_*` primitive once per target behind `#if defined(__x86_64__)` (real
instruction) / `#else` (no-op stub) — so the same `.spl` source compiles on
every target without inline target-specific asm. `_halt()` did not follow
that idiom; it hardcoded raw x86 mnemonics in an `asm """ ... """` block.

**Fix:** `_halt()` now calls two new externs, `rt_cli()` / `rt_hlt()` (reusing
the runtime-func names already registered in `runtime_sffi.rs` and already
used by `x86_64/cpu.spl`), in a `while true: rt_hlt()` loop instead of the
inline `cli`/`hlt`/`jmp` block. `runtime_minimal.c`'s `rt_hlt()` stub gained a
`#elif defined(__riscv)` branch emitting a real `wfi` (wait-for-interrupt)
instruction — mirroring the `wfi()` already used by
`os.kernel.arch.riscv64.cpu.Rv64Cpu.cpu_halt_loop()` — instead of the generic
empty no-op, so riscv64 gets a genuine halt rather than a busy-spin.
`rt_cli()`/`rt_sti()` were deliberately left as plain no-ops on riscv64 (not
given a CSR-based SIE-clear branch): riscv64 already has its own IRQ-mask path
(`os.kernel.arch.riscv64.cpu.csrc_sstatus(SSTATUS_SIE)`), and `_halt()` in
`idt.spl` is only reached from x86 IDT exception handlers, so it is dead code
on riscv64 — correctness there means "compiles and links", not "masks IRQs".
The x86_64 branch of `runtime_minimal.c` (`#if defined(__x86_64__)`, lines
182-249) was not touched.

**Files:** `src/os/kernel/interrupts/idt.spl`,
`src/runtime/startup/baremetal/runtime_minimal.c`.

**Verified** (rebuilt Rust seed unaffected — no Rust changed; ran the exact
riscv64 full-kernel `native-build` command from the 2026-08-06 update above):
- Before this fix (still true from the update above):
  `Build failed: compile inline asm C failed: .../simple_asm_blocks.c:445:12:
  error: unrecognized instruction mnemonic` (`cli`/`hlt`/`jmp`).
- After this fix: that error is gone entirely (0 occurrences of "unrecognized
  instruction mnemonic" in the build log). The riscv64 closure now compiles
  every `.spl` and reaches the **link** stage, where it hits a new, later,
  unrelated blocker: `ld.lld: error: undefined symbol: rt_enum_id` /
  `rt_native_cmp` / `rt_string_new_literal`, plus an undefined
  `os__kernel__arch__riscv64__boot__boot_main` referenced from
  `simple_asm_blocks.c` — a link-graph/object-selection gap, not an asm or
  codegen defect. Out of scope for this task; needs its own tracked item.
- x86_64 regression check: rebuilt the x86_64 kernel closure
  (`--entry src/os/kernel/arch/x86_64/boot.spl --target x86_64-unknown-none`)
  — `Build complete: 7 compiled, 0 cached, 0 failed`, links successfully.
  `_halt()`'s x86_64 behavior is semantically equivalent (same `cli` once then
  `hlt`-in-a-loop), not byte-identical asm (extern calls through the runtime
  ABI replace one static inline-asm block); the untouched `#if
  defined(__x86_64__)` branch of `runtime_minimal.c` guarantees the C-level
  `rt_cli`/`rt_hlt` implementations themselves are unchanged.
- Sabotage test: reverted only `idt.spl`'s `_halt()` back to the raw
  `asm """cli\n.Lhalt_loop:\nhlt\njmp .Lhalt_loop"""` block, reran the
  identical riscv64 build command — the exact original
  `simple_asm_blocks.c:445:12: error: unrecognized instruction mnemonic`
  failure reproduced verbatim (plus two more mnemonic errors at columns 47/60
  for `.Lhalt_loop:`/`jmp`). Restored the fix and re-verified it builds past
  that point again.
- Sibling scan: grepped every non-`arch/x86*` kernel/services `.spl` file for
  `asm """` blocks containing x86-only mnemonics (`cli|sti|hlt|lgdt|lidt|ltr|
  invlpg|rdmsr|wrmsr|outb|inb|outw|inw|outl|inl|iretq|lretq|mov %cr|swapgs`) —
  `idt.spl`'s `_halt()` was the only match; no known siblings remain.

## FIXED 2026-08-06: `boot_main` "undefined symbol" was a stale hardcoded
mangled-name mismatch in `boot.spl`, not a link-graph/object-selection bug

Investigated why the kernel's own entry point,
`os__kernel__arch__riscv64__boot__boot_main`, was reported undefined by
`ld.lld` even though it is trivially reachable from the entry closure. `nm`
on every kept object in `.simple/native-objects-*` after a reproduction of
the exact command above showed the *defined* symbol for `boot_main` was
`src__os__kernel__arch__riscv64__boot__boot_main` (mod_223.o, `T` binding) —
i.e. **with** a `src__` prefix — while `simple_asm_blocks.o` (compiled from
`boot.spl`'s raw `asm volatile` `_start` stub) referenced it **without** that
prefix. Root cause traced to
`src/compiler_rust/compiler/src/pipeline/native_project/mod.rs`'s
`source_root_for_file` / `common_ancestor_of_dirs`: when more than one
`--source` dir is valid, the compiler relativizes every module's path against
the **common ancestor** of *all* configured `--source` roots, not against
whichever root actually contains the file. This build's flags
(`--source build/os/generated --source src/os --source src/lib`) have a
common ancestor of the repo root (since `build/` and `src/` diverge at the
first path component) — so `boot.spl`'s module path becomes
`src.os.kernel.arch.riscv64.boot`, one segment longer than the `os.kernel...`
path a single-root build (`--source src` or `--source src/os`) would produce.
`boot.spl`'s inline asm hardcoded the shorter/older name.

Sibling scan of every riscv/riscv64 boot file with a similar hardcoded
`call <mangled_name>` in raw asm found **three different prefix conventions**
already in the tree (evidence this class of bug is systemic, not a one-off):
`os__kernel__arch__riscv64__fpga_boot__fpga_boot_main` (fpga_boot.spl),
`kernel__arch__riscv64__boot_hosted_probe__boot_main` (boot_hosted_probe.spl,
2 segments shorter), `os__kernel__arch__riscv32__boot__boot_main`
(riscv32/boot.spl) — each was evidently authored/last-verified against a
different `--source` flag combination. Only `riscv64/boot.spl` (the one this
task's exact build command uses) was fixed; the siblings are out of scope
here (not on this build's entry path) but are flagged as the same defect
class — see "Open: systemic risk" below.

**Fix:** `src/os/kernel/arch/riscv64/boot.spl`'s `_start()` asm now calls
`src__os__kernel__arch__riscv64__boot__boot_main` (was
`os__kernel__arch__riscv64__boot__boot_main`), with an inline comment
explaining the `common_ancestor_of_dirs` mangling dependency so a future
`--source` flag change doesn't reintroduce this silently.

**Verified:** rebuilt (no Rust changes needed — pure `.spl` fix) and reran
the exact riscv64 full-kernel `native-build` command. Before: `ld.lld: error:
undefined symbol: os__kernel__arch__riscv64__boot__boot_main` (plus the
`rt_enum_id`/`rt_native_cmp`/`rt_string_new_literal` errors below). After:
that specific error is gone; the link now fails only on genuine runtime-symbol
gaps (next section) — i.e. the build progressed past the link-graph confusion
into what is actually the next real blocker.

**Open: systemic risk (not fixed, flagging only).** This class of bug — a raw
`asm` block hardcoding a module's mangled symbol name, which depends on the
full `--source` flag set at build time — will recur any time the `--source`
flags change, for *any* of the sibling files listed above, or for
`riscv64/boot.spl` itself if this build command's `--source` list is ever
edited. A more robust fix (e.g. having the compiler substitute a
placeholder/intrinsic for "this module's own symbol name" instead of forcing
`.spl` authors to hardcode it) is out of scope for this task but worth its
own tracked item.

## NEW BLOCKER (not fixed, documented): riscv64 freestanding runtime is
missing ~16 `rt_*` primitives that the full kernel closure now needs

With the `boot_main` fix above, the link now fails on a different, larger set
of undefined symbols (lld's default `--error-limit=20` stopped it at exactly
20; re-running with `--error-limit=0` would likely show more from the same
family):

```
rt_native_cmp, rt_array_copy, rt_array_pop, rt_dict_new, rt_dict_remove,
rt_enum_discriminant, rt_enum_id, rt_load_barrier, rt_string_char_at,
rt_string_new_literal, rt_string_replace, rt_string_rfind,
rt_string_to_byte_array, rt_string_to_int_lenient, rt_string_to_lower,
rt_volatile_read_u32, rt_volatile_read_u64, rt_volatile_write_u32,
rt_volatile_write_u64
```
(plus one unrelated `_parse_lfn_slot` — a reference/definition name mismatch
in `src/os/kernel/fs/fat32.spl`'s `fat32_parse_lfn_slot`, out of scope: that
file is under active work by a separate concurrent lane per this task's
briefing, left untouched.)

Root-cause category: **(a) genuinely missing runtime archive/objects**, not a
build-flag bug or compiler mangling bug. Confirmed via
`grep -rln "rt_dict_new\|rt_enum_id\|..." src/runtime`: every one of these 16
symbols is implemented **only** in the hosted runtime
(`src/runtime/runtime.c` / `src/runtime/runtime_native.c`), which is not part
of the freestanding riscv64 build. The freestanding baremetal runtime
(`src/runtime/startup/baremetal/runtime_minimal.c`) is a much smaller,
independent reimplementation (~32 `rt_*` functions total) that never grew
equivalents for dict, several string ops, enum reflection
(`rt_enum_id`/`rt_enum_discriminant`), `rt_native_cmp`, or the
`rt_volatile_read/write_u32/u64` MMIO helpers (only `_u8`/`_u16` widths and a
disjoint symbol set exist there today). This is unlike the earlier
`_halt()`/`rt_hlt()` fix in this doc, which was a single missing per-arch
branch in an existing function — here the functions don't exist in the
freestanding runtime at all, in any arch branch.

**Why not fixed in this pass:** several of the missing symbols
(`rt_dict_new`, `rt_string_replace`/`rt_string_to_lower`/etc., `rt_enum_id`/
`rt_native_cmp`) require real design decisions specific to a baremetal
freestanding context — is there a heap allocator available yet at the point
these are called from init closures, what backs dict storage without the
hosted GC/allocator, how is enum-identity/reflection metadata represented
without the hosted runtime's type tables — that a rushed implementation risks
getting subtly wrong in kernel code. The `rt_volatile_read/write_u32/u64`
quartet by contrast look mechanically trivial (single-instruction MMIO
wrappers, precedent already exists for `_u8`/`_u16` and for the hosted
`_u32`/`_u64` versions at `runtime_native.c:4883-4906`) and would be a safe
follow-up, but the other ~12 are the real, larger work item. Needs its own
tracked item / dedicated pass rather than a rushed subset landing here.

**Evidence:** reproduction command and log excerpt as in the section above;
`nm` output on `.simple/native-objects-*/mod_223.o` for the mangling
diagnosis is not preserved (temp build dir), but is trivially reproducible by
rerunning the exact command in this doc and inspecting the kept objects path
printed on link failure (`Link failed. Objects kept at: ...`).
