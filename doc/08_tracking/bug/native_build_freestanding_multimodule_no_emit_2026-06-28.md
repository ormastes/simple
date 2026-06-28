# native-build: freestanding multi-module entry exits 255 with no binary, no error

Date: 2026-06-28

Lane: `.spipe/simpleos-alpine-harden-musl-busybox` (AC-6b — cross-compile simplebox)

## Summary

`bin/simple native-build` cannot cross-compile a multi-module SimpleOS userland
entry (simplebox) to a real binary in the current seed. It loads the import
closure, prints only lint/gc warnings, then exits **255** producing **no output
file and no error diagnostic**.

## Evidence (this session)

Sysroot was built for real first (so this is NOT a missing-sysroot issue):
`build/os/sysroot/lib/libsimpleos_c.a` (137 KB), `crt0.o`, `share/simpleos/simpleos.ld`,
and headers all present (`sh src/os/port/llvm/sysroot.shs`, exit 0).

| entry | command | result |
|---|---|---|
| trivial `fn main`, **no imports** | `native-build --entry tiny.spl -o tiny.out` | **ELF, 19632 bytes, runs** (`llc-object`, `write-at:done`) |
| **simplebox** (imports os.tools + os.libc) | `native-build --backend llvm --source src/os --source src/lib --entry src/os/tools/simplebox/simplebox_main.spl --entry-closure --target x86_64-unknown-none --linker-script .../simpleos.ld -o .../simplebox` | **exit 255, no binary, warnings only, no error** |
| documented `kernel_entry.spl` (multi-module) | `native-build --source src/os --source src/lib --entry .../kernel_entry.spl --target x86_64-unknown-none -o test-kernel.elf` | exit 0, **no binary emitted** |

The discriminator is cross-module imports: an import-free entry emits a real
ELF; any entry pulling a module closure fails to emit. Host target (no `--target`)
behaves the same for the multi-module entry. `--entry-closure` and `--backend
llvm` do not change the outcome. Memory was not the limit (118 GB free).

This matches the known seed native-build cross-module gap (full-program codegen
drops cross-module symbols; `run`/`-c` no-op on large import graphs).

## Impact

The userland->image wire is complete and verified at the Simple level (simplebox
entry consumes the pure-Simple libc, 8/0; build command is canonical, 7/0; image
builder packs /bin/simplebox), but the **actual cross-compiled binary cannot be
produced** until native-build emits for multi-module freestanding entries. The
image pack falls back to its placeholder until then.

## Acceptance for closure

- `native-build --target <triple>-none --entry-closure` on a multi-module entry
  (e.g. simplebox_main.spl) emits a real freestanding ELF linked against the
  SimpleOS sysroot, OR fails with a concrete error (not silent exit 255).
- Then `build_simplebox("x86_64-unknown-none")` produces a runnable
  `build/os/rootfs/bin/simplebox`, and `simplebox seq '  2'` proves libc_strtoul
  executes in the compiled binary.
