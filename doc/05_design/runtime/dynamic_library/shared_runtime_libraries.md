# Shared (Dynamic) Runtime Libraries

Status: Linux shared library is real and shippable; Windows is build-correct but
untested; SimpleOS cannot load one at all. Measured 2026-09-06 on
aarch64-unknown-linux-gnu.

Owner directive: *Simple must use dynamic libs, not static archives.* This
document covers how the runtime libraries are **built and shipped**. Which
library the Stage-4 compiler entry *selects* is owned elsewhere
(`src/compiler_rust/compiler/src/pipeline/native_project/**`) and is deliberately
not changed here.

## Inventory

| Artifact | Platform | Kind | Produced by | Consumed by |
|---|---|---|---|---|
| `libsimple_runtime.so` | Linux/macOS | dynamic | `runtime/Cargo.toml` `crate-type=[…,"cdylib"]` | nothing yet — was a build by-product |
| `libsimple_runtime.a` | all hosted | static | same crate, `staticlib` | freestanding/bootstrap lanes |
| `libsimple_runtime.rlib` | all | rlib | same crate | Rust-to-Rust deps (`simple-native-all`) |
| `libsimple_native_all.a` | all hosted | **static only** | `native_all/Cargo.toml` `crate-type=["staticlib"]` | **Stage 4 links this** |
| `libsimple_compiler_backfill.a` | all hosted | **static only** | `compiler_backfill/Cargo.toml` | full-CLI bootstrap |
| `libspl_fonts` | all | cdylib | `spl_fonts/Cargo.toml` | font assets |

`simple-native-all` and `simple-compiler-backfill` are static-only by
declaration. `simple-runtime` already declared `cdylib`, so a `.so` was being
produced — but as a by-product, not an artifact.

## What changed

`src/compiler_rust/runtime/build.rs` gained `emit_cdylib_soname()`, which emits
`cargo:rustc-cdylib-link-arg=-Wl,-soname,libsimple_runtime.so.<major>` on ELF
platforms and `-install_name @rpath/…` on Mach-O.

`rustc-cdylib-link-arg` is the correct lever because it applies **only** to the
cdylib link step: the `rlib` and `staticlib` outputs of the same crate are
untouched, so the static lane is unaffected. Putting `-soname` in
`.cargo/config.toml` rustflags would stamp it onto every crate in the workspace,
including binaries.

Without `DT_SONAME` a consumer records the *build path* it linked against in
`DT_NEEDED`; the library can never be installed, versioned, or resolved from a
system directory. With it, an install step becomes mandatory — which is what
`scripts/setup/install-runtime-shared-library.shs` provides, creating the
conventional three-name layout:

```
libsimple_runtime.so.0.1.0   real file
libsimple_runtime.so.0  -> …  the SONAME; ld.so resolves this
libsimple_runtime.so    -> …  link-time name for -lsimple_runtime
```

The static archive is installed **alongside**, never instead: freestanding
targets still require it, and breaking that would be a worse regression than the
one being fixed.

`scripts/check/check-runtime-shared-library.shs` asserts the artifact exists, is
an ELF `DYN`, carries `DT_SONAME`, and exports a non-vacuous `rt_*` surface above
a recorded floor.

## Known gap: the C half of the runtime is not exported

Measured, and tracked in
`doc/08_tracking/bug/cdylib_hides_c_runtime_exports_2026-09-06.md`:

All four figures below are measured from the **same tree** (this branch, this
target dir) so the comparison is apples-to-apples:

| surface | exported `rt_*` |
|---|---|
| `libsimple_native_all.a` (what Stage 4 links) | **2244** |
| `libsimple_runtime.so` | **1676** |
| gap | **568** |
| …of which C-defined objects inside the `.so` | **350** (0 exported) |

(For provenance: the pre-existing bootstrap baseline `.so` exports 1646 and its
`native_all` 2211. Those come from an older commit and must not be mixed with
the same-tree numbers above; the 1646→1676 delta is the newer `rt_cache_host_*`
family, not a build difference.)

The 350 C symbols are a **subset** of the 568 gap, not the whole of it: the
remaining ~218 are `simple-native-all`-only names (driver hooks, `rt_cocoa_*`,
`rt_win32_*`) that were never in the runtime crate at all.

`build.rs` compiles ~40 owned C translation units into the cdylib and links them
with `+whole-archive`, so the code *is* in the library — `rt_time_now_nanos`
resolves as a local `t` symbol, not a global `T`. The cause is rustc's cdylib
export list, confirmed by measurement rather than inference: `--print link-args`
shows rustc passing `--version-script=<generated list>`, and `build.rs` sets no
`-fvisibility=hidden` (the only `.flag()` call in the file is `-xobjective-c`),
so compile-time visibility is not what demotes them. A version script's
`local: *` clause binds every unlisted symbol locally, which is exactly the `t`
that `nm` reports. `--export-dynamic-symbol=rt_*` was tried and measured to have
no effect. No symbol-table accessor is exported either, so those 350 providers
are unreachable from outside the library by any route.

**Consequence for the selection lane:** `libsimple_runtime.so` is not yet a
drop-in replacement for `libsimple_native_all.a`. It must not be selected for a
direct native link until this gap closes.

## Windows

Untested on this host — no Windows Rust target is installed, so not even
`cargo check --target` was run. Do not read this section as a working build.

`emit_cdylib_soname()` correctly no-ops: PE/COFF has no SONAME, and the DLL name
is embedded in the import library rustc emits. rustc produces
`simple_runtime.dll` plus `simple_runtime.dll.lib` (MSVC) or
`libsimple_runtime.dll.a` (MinGW), exporting the Rust `#[no_mangle]` surface
automatically.

The same 350 C `rt_*` symbols are missing from the DLL export table for the same
root cause, and it is *not* fixable by shipping a `.def`: rustc already passes
its own generated `.def`, and a second one conflicts. The fix has to be the one
described in the bug record (build.rs-generated `#[no_mangle]` shims, or the C
sources as their own shared library), not a link flag.

## SimpleOS

**SimpleOS cannot load a shared library, and shipping a `.so` for it would be
fabrication.** It loads static, non-PIE `ET_EXEC` ELF only.

- `src/os/kernel/loader/elf_loader.spl` errors on anything but `ET_EXEC`; it has
  no `PT_DYNAMIC`/`PT_INTERP` handling.
- `dlopen`/`dlsym` (syscalls 65/66/67 → `src/os/kernel/loader/dylib_registry.spl`)
  are a symbol-table *query* service over kernel-held bytes. That file states the
  resolved value "is not yet a callable host function pointer" — nothing is
  mapped or relocated.
- `src/os/kernel/arch/common/relocations.spl` defines `R_AARCH64_RELATIVE`,
  `R_X86_64_JUMP_SLOT`, `GLOB_DAT` — orphaned constants with no consumer.
- `doc/07_guide/os/simpleos/simpleos_executable_format.md` states it outright:
  "Only static linking is supported."
- Every `*-unknown-simpleos` target spec sets `"relocation-model": "static"` and
  omits `"dynamic-linking"`, so rustc hard-errors on `crate-type=["cdylib"]`.

Required before a `.so` could load, in dependency order: accept `ET_DYN` and pick
a load base; parse `PT_DYNAMIC`; implement a relocation engine over the orphaned
verbs; map into the *target* process address space with a W^X/mprotect step;
global/local symbol scope with `DT_NEEDED` recursion and refcounting; decide
kernel-side linker vs. a real `/lib/ld-simpleos.so.1`; toolchain `-fPIC -shared`
plus `simpleos.ld` gaining `.dynamic/.dynsym/.rela.*/.got`; and per
`.claude/rules/board-runnable.md`, real-firmware evidence — no loader capability
here is board-proven today, and the existing dynload exercises run in a host
process, not a booted guest.

## Not addressed here (other lanes)

`libgcc_s.so.1` appears in `ldd` and 12 undefined `_Unwind_*` symbols remain.
This is **identical on the pre-existing bootstrap baseline** and is unchanged by
this work; removing unwind machinery is a separate lane.
