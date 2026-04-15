# LLVM SimpleOS Cross-Build

Builds a statically-linked cross `clang` (with embedded LLD) targeting SimpleOS.
Requires `ormastes/llvm-project:simpleos @ b0e410881` (Phase 2 embed-LLD patches).

## Prerequisites

| Item | Notes |
|------|-------|
| Host tools | `cmake ninja-build clang` — `sudo apt-get install -y cmake ninja-build clang` |
| LLVM source | `git clone -b simpleos https://github.com/ormastes/llvm-project $HOME/llvm-project` |
| SimpleOS sysroot | `bin/simple run src/os/port/llvm/sysroot.shs` |
| Disk space | ~2 GB cross build tree, ~120 MB final clang binary |

## Invocation

```bash
# defaults: LLVM_SRC=$HOME/llvm-project, LLVM_BUILD=build/os/llvm/cross-x86_64
scripts/build_llvm_simpleos_cross.sh

# custom paths
LLVM_SRC=/opt/llvm-simpleos \
LLVM_BUILD=/tmp/llvm-cross \
SIMPLEOS_SYSROOT=build/os/sysroot \
JOBS=16 \
scripts/build_llvm_simpleos_cross.sh

# dry-run (print commands, do not execute)
LLVM_BUILD_DRY_RUN=1 scripts/build_llvm_simpleos_cross.sh
```

## Expected Output

- `build/os/llvm/cross-x86_64/bin/clang` — cross compiler (~120 MB)
- Smoke-test: `build/os/llvm/cross-x86_64/bin/clang --target=x86_64-simpleos --sysroot=build/os/sysroot -c examples/simpleos_hello_c/hello.c -o /tmp/hello.o`

## Troubleshooting

**tblgen-not-found** — CMake cross stage fails with `Could not find llvm-tblgen`.
Delete `build/os/llvm/host-tools` and re-run; the script rebuilds it automatically.

**missing sysroot** — Exit code 2: `bin/simple run src/os/port/llvm/sysroot.shs` must
complete successfully before invoking this script.

**ENABLE_PIC mismatch** — If an existing `CMakeCache.txt` has `LLVM_ENABLE_PIC=ON`,
delete `$LLVM_BUILD/CMakeCache.txt` and re-run. Static SimpleOS requires `LLVM_ENABLE_PIC=OFF`.

**wrong branch** — Script warns (does not fail) if `LLVM_SRC` is not on `simpleos`.
The Phase 2 embed-LLD patch (`CLANG_SIMPLEOS_EMBED_LLD`) is only present on that branch.
