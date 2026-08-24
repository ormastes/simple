# Simple cannot be built for SimpleOS on any arch: the target simple-core archive never reaches the link line (2026-08-24)

- Status: **FIXED for aarch64** at `6a1d98f9c10` (2026-08-24, Lane F). riscv64 now
  resolves every symbol and fails one step later on a separate, unrelated defect:
  `simpleos_riscv64_crt0_weak_undef_pcrel_out_of_range_2026-08-24.md`.
  x86_64 still has no sysroot producer (unchanged).
- **CORRECTION (2026-08-24, measured): the "1-3 genuinely missing symbols" claim
  below is FALSE. Nothing was missing.** `rt_string_new_literal`, `rt_native_cmp`
  and `rt_unwrap_or_trap` are all defined in `src/runtime/runtime_native.c`, which
  the sysroot producers already cross-compile into
  `<sysroot>/lib/libsimpleos_all.a` -- that archive defines **761** `rt_*` symbols
  (vs the core archive's 316), including all three. They read as missing only
  because the cross-check was made against the core archive alone, while the link
  line was in fact carrying neither archive. `simpleos_guest_arch_id` is a
  different thing again: an unbacked `extern fn` in
  `src/app/simpleos_tool/guest_target.spl`, not a runtime symbol, and it does not
  appear in the current build. The ONLY genuinely absent symbol was
  `__extenddftf2`, a compiler-rt builtin -- see "What the fix actually was".
- Status was: OPEN (P1 for the SimpleOS bootstrap goal)
- Measured in `/mnt/data/worktrees/goal-lane-c-simpleos-arch` at `22615820e65`.
- Companion to `simpleos_guest_simple_cli_staged_but_never_executed_2026-08-24.md`.

## Verdict per architecture

| target | can Simple be built for SimpleOS? | blocker |
|---|---|---|
| `x86_64-unknown-simpleos` | **NO** | no sysroot producer exists at all |
| `aarch64-unknown-simpleos` | **NO** | link: 20 undefined codegen-emitted `rt_*` |
| `riscv64-unknown-simpleos` | **NO** | link: 20 undefined codegen-emitted `rt_*` |

The riscv64 receipt dated 2026-08-21 (`status=staged`) is **not** counter-evidence:
it was produced by a different compiler build on a different day, and the same
recipe re-run from source today does not link. Nothing that exists now rebuilds it.

## Evidence

Probe, before any artifacts were produced (`SEED=bin/release/x86_64-unknown-linux-gnu/simple`):

```
$ sh scripts/ci/build-simpleos-toolchain.shs --probe-only     # rc=1
  x86_64-unknown-simpleos: FAIL no valid sysroot for x86_64-unknown-simpleos (first candidate: missing build/os/sysroot-x86_64/lib/crt0.o)
  aarch64-unknown-simpleos: SKIP arch not yet buildable: no valid sysroot ...
  riscv64-unknown-simpleos: SKIP arch not yet buildable: no valid sysroot ...
RESULT: FAIL
```

Both non-x86 prerequisites then built CLEAN from source in this worktree:

- `sh scripts/os/simpleos-sysroot-riscv64.shs` rc=0 (crt0.o, libsimpleos_c.a, libsimpleos_all.a, simpleos.ld)
- `sh scripts/os/simpleos-sysroot-aarch64.shs` rc=0 — `[sysroot-aarch64] done: build/os/sysroot-aarch64`
- `sh scripts/os/simpleos-core-archive.shs --target riscv64-unknown-simpleos --backend cranelift`
  -> `archive=build/os/simple-core-simpleos-riscv64/libsimple_runtime.a parts_built=19 parts_failed=0`
- same for aarch64 -> `parts_built=19 parts_failed=0`

So sysroot and runtime-archive production are **not** the blocker on aarch64/riscv64.
With them present the CI wrapper reaches a real build and fails at LINK:

```
$ sh scripts/ci/build-simpleos-toolchain.shs --only aarch64      # rc=1
  aarch64-unknown-simpleos: FAIL native-build failed (rc=8, ...)
Build failed: link failed: ld.lld: error: undefined symbol: rt_alloc
ld.lld: error: undefined symbol: rt_string_new_literal
... 20 distinct undefined symbols, "referenced 978 more times"
```

## Root cause: the archive is resolved, reported, and then not linked

`nm --defined-only build/os/simple-core-simpleos-riscv64/libsimple_runtime.a` defines
**316** `rt_*` text symbols. Cross-checking the 20 undefined names against that archive:

- with `SIMPLE_SIMPLE_CORE_PATH=<dir>`: **19 of 20 are DEFINED in the archive**; only
  `rt_string_new_literal` is genuinely absent.
- with `SIMPLE_SIMPLE_CORE_PATH=<...>/libsimple_runtime.a`: 17 of 20 defined; absent are
  `rt_native_cmp`, `rt_string_new_literal`, `simpleos_guest_arch_id`.
- `grep -c libsimple_runtime.a` over the whole build log: **0** — the archive path never
  appears in the link invocation.

A symbol that is defined in the archive the build was *told* to use, and still undefined at
link, means the archive is not on the link line. This is a link-wiring defect, not a missing
runtime: the CI even prints `runtime_archive=build/os/simple-core-simpleos-<arch>/libsimple_runtime.a`
immediately before the build it does not pass it to. Neither env spelling (file or directory)
changes the outcome. Same shape on aarch64 (`rt_alloc` is defined in its archive and still
reported undefined).

Genuinely missing beyond the wiring bug — must also be fixed, but they are 1-3 symbols, not 20:
`rt_string_new_literal` (both arches), `rt_native_cmp`, `simpleos_guest_arch_id`.
`rt_unwrap_or_trap` appears in this undefined set, tying it to
`stage3_native_build_and_compile_segv_on_hello_world_2026-08-18` and the ADVISORY-RED
`scripts/check/check-no-unresolved-runtime-symbols.shs`.

## x86_64 is blocked one step earlier

`grep -rn "sysroot-x86_64" scripts/ src/` returns **nothing**. `scripts/os/` ships
`simpleos-sysroot-aarch64.shs` and `simpleos-sysroot-riscv64.shs` and no x86_64 sibling,
while `src/app/ci/build_simpleos_toolchain.spl:131` probes `build/os/sysroot-<arch>` for
all three and the CI header states x86_64 "must go green". The producer was never written.

## Not the cause (ruled out by measurement)

- Host C toolchain: `cc`, `clang`, `gcc`, `ar`, `llvm-ar`, `ranlib` all present;
  `sh scripts/check/check-c-runtime-compiles-push.shs` -> `PASS — 118 file(s) compiled, 0 errors
  (2 skipped for unavailable external dependencies)`, rc=0.
- The first riscv64 CI failure was `timeout (300s)` on one file under host load ~40-100.
  Re-run directly with `--timeout 1800` it compiles fine and fails at the SAME link step —
  so the timeout was environmental noise, not the blocker.
- A first archive attempt failed with `error: native backend 'llvm' is not available in this
  build; rebuild the Rust driver with --features llvm or use --backend cranelift`. That is the
  deployed seed lacking the `llvm` cargo feature (see CLAUDE.md's inkwell/LLVM pin);
  `--backend cranelift` — what the 2026-08-21 build stamp itself records — builds all 19 parts.

## What the fix actually was (2026-08-24, `6a1d98f9c10`)

The diagnosis "the archive is resolved, reported, and then not linked" was exactly
right. `NativeProjectBuilder::simpleos_user_runtime_paths()` in
`src/compiler_rust/compiler/src/pipeline/native_project/linker.rs` is the only
thing that puts a runtime on the freestanding link line, and it failed four ways:

1. its arch guard was `X86_64 | Aarch64`, excluding **Riscv64** entirely -- so
   riscv64 got no crt0, no libc and no runtime at all;
2. it looked for the runtime only at `<sysroot>/lib/libsimple_runtime.a`, a path
   **no sysroot producer creates**, and never consulted `SIMPLE_SIMPLE_CORE_PATH`
   (which is how the separately-built core archive is communicated) -- so the
   archive the CI resolved and echoed as `runtime_archive=` was never passed on;
3. the all-or-nothing `crt0 && runtime && libc` test silently returned `None`
   when the runtime was missing, dropping **crt0 and libc too**;
4. it linked `libsimpleos_c.a` (libc ALONE) rather than `libsimpleos_all.a`
   (libc + the cross-compiled `src/runtime` C runtime), leaving every C-runtime
   symbol undefined -- this is what made three present symbols look missing.

Also fixed: riscv64 mapped to the x86_64 unsuffixed `build/os/sysroot` instead of
`build/os/sysroot-riscv64`, and `resolve_freestanding_linker_script` carried the
same `X86_64 | Aarch64` guard so riscv64 never got the sysroot's `simpleos.ld`.
A SimpleOS link whose inputs cannot be resolved now **fails closed** with an
actionable message instead of silently linking with no runtime.

Measured result: undefined `rt_*` went **20 -> 0 on both arches**. One genuinely
absent symbol was then exposed on both, `__extenddftf2` -- the binary64 ->
binary128 compiler-rt builtin, needed because `long double` is IEEE quad on both
ABIs and `strtold()` is `(long double)strtod(...)`, while these freestanding
targets have no compiler-rt (`cc -print-libgcc-file-name` returns nothing for
`aarch64-none-elf` / `riscv64-unknown-elf`). Implemented as a real exact
conversion in `src/os/libc/simpleos_softfloat_builtins.c`, validated bit-identical
against the compiler's own conversion over all edge cases (signed zeros,
subnormals incl. the minimum, inf, NaN) plus 300,000 random doubles.

Final state:

| target | result |
|---|---|
| `aarch64-unknown-simpleos` | **PASS** -- `bin/release/aarch64-unknown-simpleos/simple`, 4393120 bytes, first PT_LOAD 0x50000000 |
| `riscv64-unknown-simpleos` | 0 undefined symbols; blocked on `simpleos_riscv64_crt0_weak_undef_pcrel_out_of_range_2026-08-24.md` |
| `x86_64-unknown-simpleos` | unchanged -- no sysroot producer exists |

## Remaining fix order

1. ~~Pass the resolved target `simple-core` archive to the link.~~ DONE.
2. ~~Add the 1-3 genuinely missing symbols.~~ Void -- none were missing; the one
   real gap, `__extenddftf2`, is DONE.
3. Fix the riscv64 crt0 weak-undef relocation (separate record, above).
4. Write `scripts/os/simpleos-sysroot-x86_64.shs`.
