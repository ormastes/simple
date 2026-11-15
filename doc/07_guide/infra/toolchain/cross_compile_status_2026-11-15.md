# Cross-Compile Status (2026-11-15)

Status of cross-compiling the Simple compiler and how to run it.

Tags: **[V]** verified, **[U]** unverified. All landed fixes are
verification-pending: none has been verified natively yet (tagged **[U]**).

## Summary

- **[V]** Smoke links (clang + `file` only, not lint/test artifacts) passed for
  PE32+ x86-64, PE32+ Aarch64, ELF FreeBSD x86-64/aarch64, ELF RISC-V,
  ELF 80386 and ELF ARM.
- **[V]** No lint or test-runner cross artifact has been produced for any
  target yet. Phase 2 is being rebuilt with #9424 and #9427.

## How to run (WSL Ubuntu 24.04, clang 18)

1. **[U]** The phase-2 builder is the self-hosted Simple compiler (in WSL at
   `~/xc/simple-p2`). Run it with `SIMPLE_BUILD_MEMORY_RESERVE_BYTES=2147483648`.
2. **[V]** Bootstrap sanity scrubs the environment
   (`scripts/bootstrap/bootstrap-from-scratch.sh` ~2589-2611). Only the reserve
   variable above survives.
3. **[U]** After a seed rebuild, rebuild with `--invalidate-cache=stage2`.
4. Helper scripts (`xc.sh`, `xc2.sh`) are not in the repo; the method is:
   - `xc.sh`: runs `native-build` for linux-x86_64 and linux-aarch64.
   - `xc2.sh`: builds the per-target Rust runtime with cargo, then runs
     `native-build` for the target.
5. **[U]** Workaround `SIMPLE_HIR_SHARDING=0`
   (`src/app/cli/native_build_main.spl:969`) is unconfirmed and should be
   unneeded after #9427.
6. Push gates need `MUST_CHECK_PUSH_BUDGET_S=600` on loaded hosts and still run
   every gate. Never use `--no-verify`.

## Toolchains

| Target family | Toolchain | Tag |
|---|---|---|
| Windows mingw x86_64/aarch64 | llvm-mingw UCRT 20260922, Linux-hosted build | [V] smoke link |
| FreeBSD amd64/aarch64 | FreeBSD 14.5 base.txz sysroots + clang `--target` | [V] smoke link |
| Linux riscv64/i686/armv7 | Debian `libc6-dev-*-cross` packages | [V] smoke link |

Gaps:
- The repo installer only fetches the Windows-hosted llvm-mingw zip; there is
  no Linux-hosted fetch. **[V]**
- Linux cross currently also uses `libgcc-13-dev-*-cross` runtime files. This
  conflicts with the no-GCC policy (use compiler-rt). **Open.**
- **[U]** Rust target `aarch64-unknown-freebsd` may need `rustup target add` or
  `-Zbuild-std`.
- Seed `-lsqlite3` is an allowed seed exception; deferred.

## Target matrix

| target | toolchain | smoke link | lint | test-runner | blocker |
|---|---|---|---|---|---|
| windows x86_64 (mingw) | llvm-mingw UCRT | PE32+ x86-64 [V] | none | none | phase-2 rebuild, llc-18 defect |
| windows aarch64 (mingw) | llvm-mingw UCRT | PE32+ Aarch64 [V] | none | none | #9373 verification-pending; phase-2 rebuild |
| freebsd x86_64 | base.txz 14.5 + clang | ELF [V] | none | none | phase-2 rebuild |
| freebsd aarch64 | base.txz 14.5 + clang | ELF [V] | none | none | Rust target std [U] |
| linux x86_64 | host clang/lld | n/a | none | none | phase-2 rebuild, llc-18 defect |
| linux aarch64 | clang + `ld.lld` | not recorded | none | none | #9391 verification-pending |
| linux riscv64 | Debian cross libc | ELF RISC-V [V] | none | none | libgcc policy conflict |
| linux i686 | Debian cross libc | ELF 80386 [V] | none | none | libgcc policy conflict |
| linux armv7 | Debian cross libc | ELF ARM [V] | none | none | libgcc policy conflict |
| linux riscv32 | none | none | none | none | Ubuntu has no glibc, no sysroot |
| simpleos x86_64/aarch64/riscv64 | `scripts/os/build-simpleos-*.shs` | not recorded | none | none | SimpleOS lane investigating |
| simpleos 32-bit | none | none | none | none | no triples (only `scripts/check/check-simpleos-x86-32-user-elf.shs`) |

## Landed fixes (all verification-pending [U])

- #9373: Windows ARM64 mingw backend (hosted_mingw_clang_target, CC reuse,
  entry-shim retarget).
- #9388: mold 2.30 aarch64 tombstone `0xfffff000` in
  `check-linked-tombstone-refs.shs`.
- #9391: Linux aarch64/riscv64 cross targets default to `ld.lld`; clang/lld/mold
  hints.
- #9393: cross-arch-bootstrap no longer forces `SIMPLE_PARSE_SHARDING=0`.
- #9395: shard pool headroom = min(24 GiB, RAM/4).
- #9424: MIR to LLVM call argument typed from the real value type when the
  callee has no known parameter types. Spec: `llvm_call_arg_stale_ptr_local_spec`.
- #9427: HIR closure digest keyed on content by default; interface keying is
  opt-in via `SIMPLE_HIR_CACHE_CLOSURE_KEY=interface`. Fixes "HIR frozen
  inventory publication failed".

## Blocked / open

- **[V]** Open llc-18 defect: `'%l28' ... expected 'ptr'` on ptrtoint in a
  message module. Fix lane in progress.
- Pre-existing failures, not regressions:
  - **[V]** `hir_cache_semantic_closure_digest_spec` fails 2/6 on base.
  - **[V]** `hir_closure_digest_interface_keyed_spec` imports the missing
    `hir_cache_iface_fallback_count`.
  - **[U]** `llvm_pointer_return_null_spec` calls a removed `translate_call`;
    not yet checked on base.
