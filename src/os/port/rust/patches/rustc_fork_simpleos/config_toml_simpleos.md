# config.toml snippet for SimpleOS targets (reference only)

Drop the block below into the fork's `config.toml` (copied from
`config.example.toml`) before running `./x.py build`. Substitute
`${SDKROOT}` with an absolute path to the SimpleOS SDK produced by
Workstream A.

```toml
# ---- SimpleOS x86_64 host/target --------------------------------------
[target.x86_64-unknown-simpleos]
cc         = "${SDKROOT}/bin/clang"
cxx        = "${SDKROOT}/bin/clang++"
linker     = "${SDKROOT}/bin/rust-lld"
ar         = "${SDKROOT}/bin/llvm-ar"
ranlib     = "${SDKROOT}/bin/llvm-ranlib"
llvm-config = "${SDKROOT}/bin/llvm-config"

# ---- SimpleOS aarch64 -------------------------------------------------
[target.aarch64-unknown-simpleos]
cc         = "${SDKROOT}/bin/clang"
cxx        = "${SDKROOT}/bin/clang++"
linker     = "${SDKROOT}/bin/rust-lld"
ar         = "${SDKROOT}/bin/llvm-ar"
ranlib     = "${SDKROOT}/bin/llvm-ranlib"
llvm-config = "${SDKROOT}/bin/llvm-config"

# ---- SimpleOS riscv64gc -----------------------------------------------
[target.riscv64gc-unknown-simpleos]
cc         = "${SDKROOT}/bin/clang"
cxx        = "${SDKROOT}/bin/clang++"
linker     = "${SDKROOT}/bin/rust-lld"
ar         = "${SDKROOT}/bin/llvm-ar"
ranlib     = "${SDKROOT}/bin/llvm-ranlib"
llvm-config = "${SDKROOT}/bin/llvm-config"

# ---- SimpleOS riscv32imac ---------------------------------------------
[target.riscv32imac-unknown-simpleos]
cc         = "${SDKROOT}/bin/clang"
cxx        = "${SDKROOT}/bin/clang++"
linker     = "${SDKROOT}/bin/rust-lld"
ar         = "${SDKROOT}/bin/llvm-ar"
ranlib     = "${SDKROOT}/bin/llvm-ranlib"
llvm-config = "${SDKROOT}/bin/llvm-config"
```

## Required env vars

| Var        | Purpose                                              |
|------------|------------------------------------------------------|
| `SDKROOT`  | Absolute path to installed SimpleOS SDK (Workstream A). |
| `PATH`     | Must contain `${SDKROOT}/bin` before host clang.     |

## Build invocation

```bash
export SDKROOT=/opt/simpleos-sdk
./x.py build --stage 1 \
    --target x86_64-unknown-simpleos,aarch64-unknown-simpleos,\
riscv64gc-unknown-simpleos,riscv32imac-unknown-simpleos \
    library/core library/alloc
```

Building full `library/std` requires Workstream B6
(`libstd_pal_simpleos`). Until then, restrict to `core` + `alloc`.
