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
4. Use the repo matrix script (replaces the ad-hoc `xc.sh`/`xc2.sh`/
   `sosxc_nb.sh`/`matrix.sh` helpers); see "Matrix script" below.
5. **[U]** Workaround `SIMPLE_HIR_SHARDING=0`
   (`src/app/cli/native_build_main.spl:969`) is unconfirmed and should be
   unneeded after #9427.
6. Push gates need `MUST_CHECK_PUSH_BUDGET_S=600` on loaded hosts and still run
   every gate. Never use `--no-verify`.

## Matrix script

`scripts/check/check-cross-compile-matrix.shs` (Linux host, e.g. WSL
Ubuntu-24.04). For each target x artifact (`lint` = `src/app/cli/lint_entry.spl`,
`test` = `src/app/test_runner_new/main.spl`) it runs preflight, a free-memory
gate, one `native-build` at a time with `SIMPLE_CACHE_SCOPE=xc-<target>`, then
checks the artifact with `file` + `llvm-readelf -h` / `llvm-readobj
--file-headers` (class and machine) and rejects an ELF with `NEEDED libgcc*`.

```sh
sh scripts/check/check-cross-compile-matrix.shs --selftest       # 22 fixtures, fatal
sh scripts/check/check-cross-compile-matrix.shs --dry-run         # plan + preflight, builds nothing
sh scripts/check/check-cross-compile-matrix.shs --list
sh scripts/check/check-cross-compile-matrix.shs --targets linux-x86_64 --artifacts lint
sh scripts/check/check-cross-compile-matrix.shs --targets linux-riscv64,linux-armv7 --run
```

Options: `--targets a,b|all` (default all), `--artifacts lint,test`,
`--builder PATH` (default `~/xc/simple-p2`, else
`bin/release/x86_64-unknown-linux-gnu/simple`), `--min-free-gb N` (default 8;
waits up to `XC_MEM_WAIT_S`=1800 s, then ERROR), `--run` (`<artifact> --help`
under qemu-user; wine is never used, so Windows/FreeBSD/SimpleOS rows are not
run), `--out DIR` (default `build/cross-matrix`). Env: `XC_TOOLCHAINS`
(default `~/toolchains`), `XC_LLVM_BIN` (default `/usr/lib/llvm-18/bin`),
`SIMPLE_LLVM_MINGW`, `SIMPLE_CROSS_RT_PREFIX`, `XC_THREADS`, `XC_TIMEOUT`.

Output: `<out>/results.tsv`, a markdown table, logs under `<out>/logs/`, and the
verdict last. Row status PASS / FAIL / ERROR (missing tool, with a fix hint) /
BLOCKED (known gap). Verdict FAIL if any row failed, else ERROR if any row could
not be checked or no row passed, else PASS (exit 0/1/2).

Hook for more targets (e.g. the NVMe FW bare-metal lane):
`XC_MATRIX_EXTRA_TARGETS=<file>`, TAB-separated rows
`name triple kind(rust|simpleos|baremetal) class(ELF32|ELF64|PE32+) arch-regex qemu extra-native-build-args`.
Extra rows join `--targets all` and are not BLOCKED.

Per-target status of the script (2026-11-16, WSL Ubuntu-24.04):

| target | preflight | lint/test build | why |
|---|---|---|---|
| linux-x86_64, linux-aarch64 | ok [V] | not run yet | box busy with other lanes' builds |
| linux-riscv64 | ok [V] | blocked | Simple AOT `.o` float ABI is not `lp64d` (see Gaps) |
| linux-i686, linux-armv7 | ok [V] | blocked | `simple-runtime` does not cargo-build for 32-bit (18-19 errors) |
| windows-x86_64, windows-aarch64 | ok [V] | not run yet | llc-18 defect / #9373 verification-pending |
| freebsd-x86_64, freebsd-aarch64 | ok [V] | not run yet | phase-2 rebuild |
| simpleos-x86_64/aarch64/riscv64gc | ok [V] | not run yet | SimpleOS lane |
| baremetal-x86/x86_64/arm/aarch64/riscv32/riscv64 | - | BLOCKED | no hosted runtime for lint/test-runner; `XC_BAREMETAL_ENABLE=1` tries a simple-core build |

## Toolchain setup

- LLVM 18: `apt install clang-18 lld-18 llvm-18 file` (mold optional; noted if absent).
- Rust: rustup + `rustup target add <triple>` per target (preflight names it).
- Linux riscv64/i686/armv7: `apt install libc6-dev-{riscv64,i386,armhf}-cross`,
  then `sh scripts/setup/build-linux-cross-compiler-rt.shs`; the cc line comes
  from `scripts/setup/linux-cross-cc.shs`. Linux aarch64: `libc6-dev-arm64-cross`.
- Windows: extract mstorsjo/llvm-mingw `<ver>-ucrt-ubuntu-22.04-x86_64` into
  `~/toolchains/` (or set `SIMPLE_LLVM_MINGW`).
- FreeBSD: extract FreeBSD 14.x `base.txz` into `~/toolchains/freebsd/{amd64,aarch64}`.
- `--run`: `apt install qemu-user`.

## Toolchains

| Target family | Toolchain | Tag |
|---|---|---|
| Windows mingw x86_64/aarch64 | llvm-mingw UCRT 20260922, Linux-hosted build | [V] smoke link |
| FreeBSD amd64/aarch64 | FreeBSD 14.5 base.txz sysroots + clang `--target` | [V] smoke link |
| Linux riscv64/i686/armv7 | Debian `libc6-dev-*-cross` libc + LLVM compiler-rt/libunwind (`scripts/setup/build-linux-cross-compiler-rt.shs`); cc line from `scripts/setup/linux-cross-cc.shs` | [V] C hello link + qemu-user run |

Gaps:
- The repo installer only fetches the Windows-hosted llvm-mingw zip; there is
  no Linux-hosted fetch. **[V]**
- Linux riscv64/i686/armv7 no longer use GCC runtime files (2026-11-16, was
  `libgcc-13-dev-*-cross` via `--gcc-install-dir`). Now: `--rtlib=compiler-rt
  --unwindlib=libunwind`, `clang_rt.crtbegin/crtend`, static LLVM libunwind
  (also served as `libgcc_s.a` = `INPUT(libunwind.a)` because Rust
  `*-linux-gnu` std asks for `-lgcc_s`), `ld.lld`. Built from LLVM 18.1.3
  release tarballs into `~/.simple/toolchains/llvm-cross-rt-18` (nothing in
  git). No `--sysroot`: Debian's `libc.so` script uses absolute paths that lld
  would re-prefix; `-B/-L/-isystem /usr/<gnu-triple>` instead. Gate:
  `sh scripts/check/check-linux-cross-no-libgcc.shs --run` (resolved inputs via
  `-Wl,--trace`, NEEDED, qemu-user) — [V] FAIL on the old config, PASS 3/3 on
  the new. **Closed for C links.** Open: i686/armv7 have no cross
  `libsimple_native_all.a` yet, so no Simple link evidence for them; a C++
  (`clang++`) link would still need libc++ instead of gcc-cross libstdc++.
  Simple rv64 hello (`simple-p2 native-build`, 2026-11-16) compiles and reaches
  `ld.lld` with this cc line, then fails: `cannot link object files with
  different floating-point ABI` — the Simple AOT `.o` is not `lp64d`. That is a
  codegen float-ABI defect, unrelated to libgcc. **Open.**
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
| linux riscv64 | Debian cross libc | ELF RISC-V [V] | none | none | none (compiler-rt, see Gaps) |
| linux i686 | Debian cross libc | ELF 80386 [V] | none | none | none (compiler-rt, see Gaps) |
| linux armv7 | Debian cross libc | ELF ARM [V] | none | none | none (compiler-rt, see Gaps) |
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
