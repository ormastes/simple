# rustc Fork Patches: SimpleOS Built-in Targets (Workstream B5)

**Purpose.** Promote the four SimpleOS target triples from `.json` custom
specs to **built-in** targets in a rustc fork, and teach `x.py` about
`simpleos` as a host/target OS.

**Fork branch.** `ormastes/rust:simpleos` (upstream: `rust-lang/rust`, base
tag matches whatever `rust-toolchain.toml` currently pins). These patches
live in-tree at `src/os/port/rust/patches/rustc_fork_simpleos/` but are
**not** applied here — apply them against a separate checkout of the fork.

**Dependency.** Workstream A (LLVM for SimpleOS) must produce a working
`$SDKROOT/bin/{clang,rust-lld,llvm-config,llvm-ar,llvm-ranlib}` before
rustc is rebuilt with these patches. Until then the specs compile but
`cargo build --target=*-unknown-simpleos` will fail at link.

## Target triples added
| Triple                          | Arch      | Notes                         |
|---------------------------------|-----------|-------------------------------|
| `x86_64-unknown-simpleos`       | x86_64    | Primary host                  |
| `aarch64-unknown-simpleos`      | aarch64   | ARM server / SBC              |
| `riscv64gc-unknown-simpleos`    | riscv64gc | RV64 general purpose          |
| `riscv32imac-unknown-simpleos`  | riscv32   | RV32 embedded / microkernel   |

## File types (IMPORTANT)
- `*.rs.patch` — **full-source** files. `cp` to
  `$RUST_FORK/compiler/rustc_target/src/spec/<name>.rs`.
- `*.patch` (not `.rs.patch`) — **unified diff**. Apply with
  `patch -p1 < FILE` from `$RUST_FORK` root.
- `*.md` — documentation only; not applied.

## Apply order
See `apply_order.txt`. Three-step process:
1. `cp` the four `*.rs.patch` full-source files into
   `compiler/rustc_target/src/spec/` (strip `.patch` suffix).
2. `patch -p1 < mod_rs_registration.patch` to register modules.
3. `patch -p1 < bootstrap_simpleos.patch` then
   `patch -p1 < rustc_llvm_build_rs.patch` for `x.py`/LLVM wiring.

Consumers drop `config_toml_simpleos.md`'s `[target.*]` block into their
`config.toml` before `./x.py build --target=x86_64-unknown-simpleos`.

## Relationship to existing JSON specs
`src/os/toolchain/rust/*-unknown-simpleos.json` become **redundant** once
these patches land in the fork, but remain forward-compatible — the
field semantics match 1:1. Delete the JSONs once the fork toolchain is
the default.
