# Windows toolchain: MinGW UCRT (MSYS2 CLANG64) by default

The default Windows build environment is **MinGW UCRT as provided by MSYS2
CLANG64**: the UCRT C runtime, clang, LLD, libunwind and libc++. No GCC is
involved anywhere.

| Piece | Default (gnu) | Explicit msvc |
|---|---|---|
| Simple triple | `x86_64-pc-windows-gnu` | `x86_64-pc-windows-msvc` |
| Rust target | `x86_64-pc-windows-gnullvm` | `x86_64-pc-windows-msvc` |
| C target / driver | `x86_64-w64-windows-gnu`, `clang.exe` | `clang-cl.exe` (`CL=/TC`) |
| Linker | LLD via `clang -fuse-ld=lld` | `lld-link` |
| LLVM C API (llvm lanes) | `bin/libLLVM-<major>.dll`, `lib/libLLVM.dll.a` | `LLVM-C.dll`, `LLVM-C.lib` |

mold cannot emit PE and is not used on Windows. The in-repo pure-Simple COFF
linker (`SIMPLE_LINKER=internal`) stays opt-in.

## Set up a host

```sh
# MSYS2, CLANG64 shell
pacman -S --needed mingw-w64-clang-x86_64-{clang,lld,llvm,libc++,libunwind}
rustup set default-host x86_64-pc-windows-gnullvm
```

Making gnullvm the default host keeps the seed's outputs at
`src/compiler_rust/target/<profile>/`. `src/compiler_rust/.cargo/config.toml`
links `*-windows-gnullvm` through `clang` + LLD. `MSYSTEM` never selects the
ABI. Git Bash always reports `MINGW64`, so `SIMPLE_WINDOWS_ABI` and
`SIMPLE_LINKER_FLAVOR` are the only switches.

## Select MSVC instead

The MSVC configuration stays in-tree and works when you select it:

```sh
export SIMPLE_WINDOWS_ABI=msvc SIMPLE_LINKER_FLAVOR=msvc
bash scripts/bootstrap/bootstrap-windows.sh --msvc ...
```

An explicit `--target x86_64-pc-windows-msvc` also selects MSVC. Defaults that
honour this switch:

- `scripts/setup/platform-detect.shs` (`PLATFORM_ABI`)
- `bootstrap-from-scratch.sh` and `bootstrap-windows.sh`
- `bootstrap-phase-toolchain.shs`
- the stage3 host-platform helper
- the seed's `Target::linker_flavor()`
- the pure-Simple `windows_link_flavor_select` and `hosted_windows_llvm_env`

## CI

CI builds **only the GNU configuration**, including release packages:

- `windows-build.yml`: seed, native_all, the seed-built compiler, then
  `--version` and a hello world.
- `rust-bootstrap-multiplatform.yml`: the `windows-cranelift` lane.
- `release.yml`: the `windows-x86_64` row.
- `phase-ladder-rung.yml`: the `windows-x86_64` lane.

Each one installs CLANG64 with `msys2/setup-msys2` (`msystem: CLANG64`) and
selects the gnullvm Rust host. `windows-aarch64` is still experimental. It
cross-builds `aarch64-pc-windows-gnullvm` with no CLANGARM64 runner, so it
stays bootstrap-only.
