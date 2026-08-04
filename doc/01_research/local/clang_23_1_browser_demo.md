<!-- codex-research -->
# Local Research: Clang 23.1 and Browser Demo

## Scope

Owned source, scripts, tests, CI, and documentation were searched for Clang/LLVM 18, 20, 23, browser-demo compilation, bootstrap linkage, and QEMU staging. Vendored runtime/compiler sources were excluded.

## Immediate production path

`scripts/check/check-simpleos-wm-fullscreen-evidence.shs` builds and admits the current-source kernel, invokes `scripts/os/build_browser_demo_client.shs`, hashes the resulting ELF, stages it as `BROWSMF.SMF`, boots UEFI/QEMU, then requires correlated scanout, font, keyboard, pointer, and browser-content evidence.

The browser builder currently defaults to `clang-20`, falls back to `ld.lld-20` or an unversioned linker, compiles `x86_64-unknown-simpleos`, rebuilds `libsimpleos_c.a` in an isolated directory, and validates ELF machine 62 plus resolved `getpid`. Its nested `make` does not receive the admitted compiler, so the browser object and libc can silently use different compiler families.

## Compiler and bootstrap surfaces

- Pure-Simple discovery stops at Clang 19/18 in `llvm_version.spl`, `llvm_capability.spl`, interpreter LLVM tools, runtime compiler, and app compile helpers.
- LLVM library loaders and diagnostics prioritize libLLVM 18 and Homebrew `llvm@18`.
- Rust bootstrap uses `inkwell 0.5` with feature `llvm18-0`; the vendored bindings stop at LLVM 18. A real LLVM 23 migration requires a binding/dependency upgrade and API compatibility work.
- Rust native-project linker/tool searches contain Homebrew `llvm@18` paths and assumptions about older `llvm-nm`, `llvm-objcopy`, and compiler ordering.
- CI installs apt/brew LLVM 18, sets `LLVM_SYS_180_PREFIX`, and has a portability test that asserts those pins.

## SimpleOS guest and tool surfaces

Guest shell manifests, packages, cross-toolchain scripts, smoke tests, and the operator guide encode `clang-20` and `/usr/bin/clang-20`. Other C payload scripts also use host `clang-20`. The migration must update one coherent tool identity rather than only the browser wrapper.

## Verification chain

1. Admit the exact provider binary and retain version/hash.
2. Admit a coherent Clang/LLD/LLVM 23.1 tool family by parsed versions.
3. Compile/link a freestanding x86_64 probe and validate ELF identity/undefined symbols.
4. Build and validate the real browser-demo ELF.
5. Run browser staging, fullscreen binary-contract, and x86 QEMU preflight specs.
6. Run ad-hoc bootstrap smoke against the admitted 23.1 family.
7. Run the canonical fullscreen QEMU wrapper and retain the full evidence bundle.

## Risks

- **Critical:** stable 23.1 does not exist on the research date; rc2 must be represented honestly.
- **Critical:** inkwell/llvm-sys ABI support is not upgraded by changing command names.
- **High:** mixed Clang 23.1 and LLD/LLVM 22 or 18 can accept source compilation but invalidate IR/LTO/tool evidence.
- **High:** nested libc/sysroot builds can silently use Apple Clang or another default compiler.
- **High:** official binaries use unversioned names inside their prefix; `clang-23` alone is not portable.
- **Medium:** guest paths and package manifests require coordinated test/doc migration.

## Cooperative review

The local inventory and gate analysis were produced by bounded read-only sidecars. The root agent is merge owner and final reviewer.

## Rust bootstrap LLVM binding boundary (2026-08-04)

The optional Rust LLVM backend cannot yet be migrated truthfully to LLVM 23.1
through a released or upstream-supported inkwell feature:

- The repository currently resolves `inkwell 0.5.0` with feature `llvm18-0`
  and `llvm-sys 180.0.0`. Its vendored inkwell manifest also stops at LLVM 18.
- Upstream inkwell `main` at commit
  `39f778fc393ee6d31d595ae1bb1c524b9d799e57` identifies itself as 0.9.0 and
  exposes LLVM features only through `llvm22-1`; its newest dependency is
  `llvm-sys 221.0.0`.
- Upstream llvm-sys `main` at commit
  `1cd2f58bbf2fdfff3903a443876b3da9918abf43` identifies itself as 221.0.1,
  declares `links = "llvm-22"`, and has no LLVM 23 binding surface.
- Therefore renaming `llvm18-0` to an invented `llvm23-1` feature, or pointing
  `LLVM_SYS_180_PREFIX` at LLVM 23, would compile against an unadmitted C API
  and cannot count as migration evidence.

### Compatibility boundary and options

1. **Wait for upstream support (preferred for production):** track an inkwell
   release/commit that adds LLVM 23.1 through a corresponding llvm-sys 231
   crate, then migrate the optional backend and run its full LLVM feature test
   matrix. Lowest maintenance risk; blocks the Rust LLVM lane until upstream
   publishes support.
2. **Maintain reviewed forks:** fork llvm-sys from 221 to a 231 binding against
   LLVM 23.1 headers/C API, then add `llvm23-1` support to an inkwell fork and
   carry it as an explicit repository dependency. This is feasible only after
   an API diff, generated-binding review, target/JIT/object tests, and license/
   supply-chain review. High effort and an ongoing maintenance obligation.
3. **Keep Rust bootstrap on Cranelift while migrating the production
   pure-Simple LLVM tool path:** this avoids pretending the optional in-process
   Rust LLVM backend supports 23.1, but it is an explicit scoped deferral rather
   than completion of the Rust LLVM migration.

No Rust dependency or lockfile change was made because none of the authoritative
upstream artifacts currently provides the requested LLVM 23.1 ABI support.

## Follow-up implementation evidence (2026-08-04)

The pure-Simple external backend needs more than the original frontend/linker
subset. A coherent provider must contain `clang`, `ld.lld`, `llc`, `opt`,
`llvm-ar`, `llvm-nm`, `llvm-objdump`, `llvm-objcopy`, and `llvm-config` from
one prefix. The signed rc2 cached build installed and validated that complete
set; the provider builder now emits canonical absolute `SIMPLE_*` handoff
paths so compiler and wrapper consumers cannot drift onto host tools.

The Rust LLVM-18 binding remains isolated rather than relabeled. A fresh
Cranelift bootstrap built and sanity-checked 728-module Stage 2 and Stage 3
artifacts, proving the bootstrap can remain LLVM-free while the resulting full
CLI owns external LLVM 23.1 execution. That run also exposed and fixed a Rust
native-project identity bug: 33 hosted modules exported the same strong
`___module_init_dynamic`; exact legacy initializers are now qualified with the
module prefix, and the focused MIR regression passed.

The first full-CLI attempt after the fix sealed Stage 3 provenance, then the
Stage 4 compiler terminated with SIGSEGV immediately after
`phase2:surface:file:released path=src/app/cli/main.spl seq=1`. The three-cycle
bootstrap cap was exhausted, so no LLVM QEMU run was started and Stage 4/QEMU
completion remains unproven. Retained logs are
`build/bootstrap-clang-23-1-stage4-cycle3.out` and
`build/bootstrap/logs/aarch64-apple-darwin/stage4-native-build.log`.
