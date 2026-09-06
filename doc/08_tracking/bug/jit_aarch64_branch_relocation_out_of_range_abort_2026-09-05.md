# `bin/simple` aborts intermittently: AArch64 JIT branch relocation out of ±128 MB range

**Filed:** 2026-09-05
**Severity:** medium — non-deterministic abort of any JIT-executed tool invocation on aarch64
**Status:** FIXED 2026-09-06 (see the section at the end) — was: open, observed once, not reproduced on demand
**Area:** Rust seed JIT (`codegen::jit`) over vendored `cranelift-jit`

## What happened

While exercising `bin/simple fmt` on small scratch files, one invocation died
with SIGABRT (rc=134) and another with SIGSEGV, on inputs that exit 0 when
re-run. The abort left a crash report:

```
Message:  assertion failed: (diff >> 26 == -1) || (diff >> 26 == 0)
Location: src/compiler_rust/vendor/cranelift-jit/src/compiled_blob.rs:90:21
OS:       linux aarch64
   8: <cranelift_jit::backend::JITModule>::finalize_definitions
   9: <simple_compiler::codegen::jit::JitCompiler>::compile_module
  10: <simple_compiler::codegen::local_execution::LocalExecutionManager …>
  11: <simple_driver::exec_core::ExecCore>::run_file_jit
  15: simple::dispatch_to_simple_app
```

`diff >> 26` is the range check for the AArch64 26-bit signed branch immediate
used by `B`/`BL` (`CALL26`/`JUMP26` relocations): ±128 MB. The assertion fires
when the JIT resolves a call whose target landed further than that from the
call site, i.e. when the JIT's code allocations are spread too far apart in the
address space.

## Why it is intermittent

The failure depends on where `mmap` places the JIT code regions, not on the
input. That is consistent with what was observed: identical inputs abort under
memory pressure (a large concurrent `native-build` was running) and exit 0 when
re-run on a quieter box. It is a latent defect, not a flake — the same
invocation can abort at any time, and the larger the JIT-compiled module the
more likely it is.

`bin/simple` JIT-compiles the tool being dispatched, so this can abort **any**
tool invocation (`fmt`, `lint`, `run`, …), not just the one observed.

## Evidence and scope

- Binary: `bin/simple` -> `bin/release/aarch64-unknown-linux-gnu/simple`
  (154,560,904 bytes, 2026-09-04 14:46) — the Rust seed.
- Crash report: `.simple/logs/crash_1508768.log` (directory is gitignored).
- 1 of the 10 crash reports present carries this assertion. The other 7 (dated
  2026-09-04) carry a different message, `can't resolve symbol
  text_dot_from_char_code`, which looks like the known unbacked-extern class
  (`unregistered_extern_silent_nil_2026-08-01.md`) rather than this one, and is
  not analysed here.

## Not fixed here

The failing assertion is in vendored code
(`src/compiler_rust/vendor/cranelift-jit/**`), which is outside the owned-code
scope, and the real fix belongs on our side of the boundary anyway: the JIT
should either allocate code regions within branch range of each other, or
emit far-call veneers / a PLT-style thunk when a target is out of ±128 MB.
Choosing between those is a design decision, so it is recorded rather than
guessed at.

## Reproduction note

No deterministic reproducer. Suggested approach: run a JIT-executed tool under
memory pressure or with ASLR forcing distant mappings, on a module large enough
to need multiple code allocations. A targeted alternative is to assert in
`JitCompiler::compile_module` that all code regions land within 128 MB and see
how often that is violated in normal runs.

## Second and third observations (2026-09-05, SOSIX unification lane)

`bin/simple lint src/lib/nogc_async_mut/sosix/file_driver.spl` (87 lines) dumped
core with the same `assertion failed: (diff >> 26 == -1) || (diff >> 26 == 0)`
(`.simple/logs/crash_2422254.log`, `JitCompiler::compile_module` via
`ExecCore::run_file_jit`), and `bin/simple lint src/lib/nogc_async_mut/sosix/fs.spl`
(276 lines) aborted the same way on its second run after reporting
`NOT LINTED: 1 file(s) could not be parsed` on its first. `lint sync.spl` in
between passed. Same binary: `bin/release/aarch64-unknown-linux-gnu/simple`,
2026-09-04 14:46. So it reproduces on demand under `lint` of these files, and
`--mode=interpreter` does not avoid it (both files dumped core again:
`crash_2425695.log`, `crash_2425892.log`). No lint verdict is obtainable for
these two files on this host until the seed is fixed; the lane records them as
**not linted**, not as clean.

## FIXED 2026-09-06 — and the abort was only half of it

Two defects, both in vendored `cranelift-jit` 0.116.1, both now patched
(`src/compiler_rust/vendor/cranelift-jit/`).

### Defect 1 — the range check is one bit too loose (silent miscompile)

`compiled_blob.rs`'s `Reloc::Arm64Call` arm asserted

```rust
let diff = ((base as isize) - (at as isize)) >> 2;   // words
assert!((diff >> 26 == -1) || (diff >> 26 == 0));    // admits +/-2^26 words
```

but `imm26` is a **signed 26-bit word** offset, so the encodable range is
`[-2^25, 2^25)` words = +/-128 MiB — matching cranelift-codegen's own
`LabelUse::Branch26 => (1 << 27) - 1` *bytes*
(`vendor/cranelift-codegen/src/isa/aarch64/inst/mod.rs:2901`). The assert
therefore admitted displacements up to +/-256 MiB; anything in the 128..256 MiB
band **passed the assert and was then truncated into a branch to a completely
wrong address**. That is why the primary reproducer here dies with SIGSEGV in
JIT code (`pc` inside a JIT mapping, garbage `x30`) rather than with the
documented SIGABRT: the abort is the *lucky* outcome, the SEGV is the same root
cause landing one bit further out. The check is now `diff >> 25`.

### Defect 2 — JIT code pages are handed out by the process allocator

`memory.rs`'s `PtrLen::with_size` uses `std::alloc::alloc`, which mixes
brk-heap and mmap'd blocks; on this host they land gigabytes apart, so two
functions of the *same* JIT module could not reach each other with a `bl`.

Fix: the *code* `Memory` of every `JITModule` (`Memory::new_code`, wired at
`backend.rs:531`) is now backed by one contiguous `mmap` reservation of exactly
`2^27` bytes — exactly the reach of a `bl` — so any two addresses inside it are
in range **by construction**. The reservation is lazy and `MAP_NORESERVE`, so an
unused module costs only address space; measured high-water mark for the vk2d
bench is **7,284 KiB of 131,072 KiB** (`SIMPLE_JIT_ARENA_STATS=1`).

Long-branch veneers (`ldr x16, #8 ; br x16 ; .quad target`, the standard
BTI-safe PLT thunk shape) are carved downwards from the top of the same arena
and cover a colocated target that lands outside it. `SIMPLE_JIT_FORCE_VENEERS=1`
routes *every* `Arm64Call` through a veneer so the path is exercised rather than
dead: the vk2d bench runs clean that way with 10,155 veneers installed.

**Stated cap:** 128 MiB of JIT code per `JITModule`. Beyond it the allocator
warns once and falls back to the old heap path, where the hazard returns — but
now with a descriptive panic naming this document instead of a bare assert.

### Before / after (same host, same build flags, aarch64)

Reproducer: `SIMPLE_LIB=src VK2D_W=800 VK2D_H=600 VK2D_RECTS=64 VK2D_FRAMES=300
simple run test/05_perf/bench/vulkan_2d_c/vk2d_bench.spl`, seed built with
`--features vulkan`.

| binary | runs | failures |
|---|---|---|
| unpatched | 8 | **2** — one `rc=139` SIGSEGV, one `rc=124` (spun at 99% CPU for the full 900 s timeout after `scene_source=table rects=64`, i.e. a corrupted branch target turned into an infinite loop) |
| patched | 8 | **0** |
| patched, `SIMPLE_JIT_FORCE_VENEERS=1` | 3 | **0** (10,155 veneers installed per run) |

`.simple/logs/crash_*.log` count went 5 -> 5 across every patched run; all five
existing reports are from unpatched runs and every one of them carries exactly
`assertion failed: (diff >> 26 == -1) || (diff >> 26 == 0)` at
`compiled_blob.rs:90`, i.e. the assert in this report. The SIGSEGV and the hang
are the *same* defect landing in the band the assert failed to catch.

Common-path regression check: `simple run` on `hello_native.spl` plus three
mid-size examples produces **byte-identical output** on the unpatched and
patched binaries, and `lint src/lib/nogc_async_mut/sosix/fs.spl` x5 adds no
crash report (it still exits 1 on a pre-existing semantic error, unchanged).

The failure is ASLR-dependent: under `gdb` with its default
`disable-randomization on` the unpatched binary does **not** crash, which is why
the original report could not reproduce on demand.

### Still red, and NOT caused by this bug

`scripts/check/check-vulkan-2d-c-compare.shs` still reports
`compare_status=skipped compare_reason=c-leg-skipped:no-vulkan-headers`: this
host has no `vulkan/vulkan.h`, so the C leg cannot build, and the script skips
the Simple leg whenever the C leg skips. The bench itself now runs to completion
but reports `status=blocked reason=backend-unavailable` —
`VulkanInstance::get_or_init` fails with `ERROR_EXTENSION_NOT_PRESENT`. Measured
cause: `vulkaninfo --summary` on this host lists 20 instance extensions and
`VK_KHR_surface` is **not** among them (only `VK_KHR_display` /
`VK_EXT_*_display` / DRM ones), so the surface extensions the backend asks for
genuinely do not exist here; there is also no `DISPLAY`/`WAYLAND_DISPLAY`. The
bench has no headless knob — `VK2D_BACKEND` only selects another backend, which
is how it falls back to `cpu`. Both are environment gaps, unrelated to the
relocation defect.

### Upstream

Both fixes belong upstream in `bytecodealliance/wasmtime`
(`cranelift/jit/src/{compiled_blob,memory}.rs`): the range check is a plain bug,
and the contiguous per-module code region is the same thing wasmtime already
does for its own allocator. Carried here as a local vendored patch, commented at
each edit site, until that lands.
