# Hosted native link fell back to gcc / bare `cc` (collect2) against the clang-only rule

- Date: 2026-11-13
- Status: FIX LANDED LOCALLY on `work/no-gcc-link-20261113` (base `98b6adbd217`, release/1.0.0), awaiting coordinator review/landing; cross-lane gaps listed below remain OPEN
- Review 2026-11-13 (HOLD on `fcae111a9b9`, fixed by follow-up commits on the same branch):
  1. BLOCKER — `crt_discovery.spl` no longer parsed: removing the `cc -print-file-name` method orphaned a
     16-space `if trace:` block (`PARSE001 unexpected token in expression: Indent`), and every importer
     (`native_linking.spl`, `shared_linking.spl`, `native_link_receipt_v1.spl`) would have failed to load.
     Fixed; `test/01_unit/compiler/backend/linker/crt_discovery_clang_probe_spec.spl` now imports the module
     (`use ... crt_discovery.*`, as native_linking does) — verified red (1/1 fail, PARSE001) with the orphan
     re-injected and green (2/2) without it. Every touched `.spl` is now parse-gated with the seed (`fmt --check`
     + `lint`), verdicts recorded in the lane report.
  2. `c_compiler_select_v1` returned the `readlink -f` realpath for a discovered hit; under a ccache masquerade
     dir (`/usr/lib64/ccache/clang -> /usr/bin/ccache`) that would run ccache bare. `CDriverProbeV1` now carries
     `invoked_path` (the PATH entry, returned) separately from `resolved_path` (realpath, classification only);
     spec case pins `/usr/lib64/ccache/clang` is returned and a masquerade whose realpath is gcc is refused.
  3. Seed `gcc_driver_refusal` exempted every triple-prefixed gcc; now only the documented hosted cross drivers
     (`DOCUMENTED_CROSS_GCC_DRIVERS`) are exempt and a host-triple `x86_64-linux-gnu-gcc-13` is refused, matching
     `c_driver_classify_v1`. `cxx_driver_for_c_driver_v1` handles `\` paths (`C:\LLVM\bin\clang.exe` -> `clang++.exe`).
- Rule: CLAUDE.md Critical Rules — "Never use GCC. Toolchain is clang + lld (mold where the target format supports it ...)"
- Spec: `test/01_unit/compiler/backend/c_driver_clang_only_spec.spl` (8/8 green after the fix, 8/8 red before)

## Symptom

A go-to-end trial link on this host (Ubuntu 24.04 aarch64, `cc` -> `/usr/bin/aarch64-linux-gnu-gcc-13`)
showed the hosted native link running through `collect2`. Two silent fallbacks caused it:

1. `native_linking.spl` (`link_native_cc` path): with no strict selector and no `SIMPLE_CC`, the
   non-cross branch set `cc = "cc"` — gcc-13 on every Debian-family host.
2. `runtime_compiler.spl::find_c_compiler()` Unix branch probed `/usr/bin/clang`, then
   `/usr/bin/gcc`, `/usr/bin/cc`, then PATH `clang, clang-18..16, gcc, cc`.

## Inventory (`git grep -nE '"gcc|/gcc|g\+\+|collect2|"cc"|"c\+\+"' -- src` + finders, vendor excluded)

| Site | Role | Before | After |
|---|---|---|---|
| `src/compiler/70.backend/backend/runtime_compiler.spl` `find_c_compiler` | hosted CC | `/usr/bin/gcc`, `/usr/bin/cc`, PATH `gcc`,`cc` fallbacks; `SIMPLE_CC` verbatim | clang-only candidates (`clang`, `clang-23`..`clang-16`); `SIMPLE_CC` probed (`command -v`, `readlink -f`, `--version` via the invoked path) and REFUSED when GCC; pure `c_driver_classify_v1` / `c_compiler_select_v1`; discovered hit returns the PATH entry (`invoked_path`), realpath classifies only |
| same file, `_find_c_compiler_windows` | Windows CC | last-resort `["clang","gcc"]` | `["clang"]` (llvm-mingw / clang-cl per CLAUDE.md) |
| `src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:~2343` | hosted link driver | `cc = "cc"` bare; `SIMPLE_CC` unverified | `find_c_compiler()` + `c_driver_admit_v1(SIMPLE_CC)`; Err with rule + fix |
| `src/compiler/70.backend/linker/crt_discovery.spl` `find_gcc_lib_dirs` | crtbegin.o probe | executes `gcc -print-file-name`, then `cc -print-file-name` | executes the selected clang; `cc` method removed. `/usr/lib/gcc/<triplet>/<ver>` dir scan kept (filesystem artifact clang itself uses on glibc) |
| `src/compiler/70.backend/linker/mold.spl` `find_linker_path` | linker | silent fallback to system `ld` (GNU ld.bfd on ELF) | fallback only on macOS (ld64); ELF: Err naming lld/mold. Explicit `SIMPLE_LINKER=ld` still honoured |
| `src/compiler/70.backend/backend/llvm_capability.spl` ar finder | archiver | Linux list ended in `"ar"` (binutils) | llvm-ar-23..16, llvm-ar only (macOS/Windows lists untouched) |
| `src/compiler/80.driver/driver_api_project_build.spl:123,144,160` | project build | bare `process_run("c++")`, `process_run("cc")` | `find_c_compiler()` + `cxx_driver_for_c_driver_v1` |
| `src/app/compile/lua_shared_lib.spl:31` | lua shared lib CC | `[..., "gcc"]` | clang-only list |
| `src/app/compile/native.spl:376`, `llvm_native_link_orchestrator.spl:224`, `runtime_compiler.spl:854` | error text | "Install clang or gcc" | clang-only text + `llvm-toolchain-env.shs` / `SIMPLE_CC=clang-23` fix |
| `src/app/cli/bootstrap_check.spl:100-120,529,552` | readiness check | PASS when `gcc` found | probes `clang` |
| `src/compiler_rust/common/src/platform/cc_detect.rs` `detect_c_compiler_for_target` | seed CC | `CC` env honoured verbatim (CC=gcc / CC=cc->gcc accepted) | `require_compiler` (called at `linker.rs:1888`, `stubs.rs:1529,1889`) now refuses via `gcc_driver_refusal` (basename gcc/g++/gcc-NN; `cc`/`c++` refused when the `--version` banner is GCC) |
| `scripts/bootstrap/repair-linux-bootstrap-runtime.shs:30` | repair compile | `${CC:-cc}` | `${CC:-clang}` |
| `scripts/bootstrap/tests/native-sanity-*-test.shs` (4) | fixture compile | `${CC:-cc}` / `${FIXTURE_CC:-cc}` | `clang` default |

### Unchanged — deliberately, with reason

| Site | Why left |
|---|---|
| `runtime_compiler.spl:253,255` `hosted_c_compiler_plan` (`aarch64-linux-gnu-gcc`, `riscv64-linux-gnu-gcc`); seed `cc_detect.rs:14-15`, `tools.rs:221-228` `hosted_linux_cross_compiler`; `scripts/bootstrap/cross-arch-bootstrap.shs:75-78` | Linux hosted CROSS lane drives the GNU cross toolchains. Replacement is `clang --target=<triple> --sysroot=/usr/<triple> -fuse-ld=lld`; verifying it needs a cross build + QEMU run, forbidden in this lane (census running). **OPEN gap, named here.** `gcc_driver_refusal` exempts triple-prefixed names on purpose so the lane keeps working. |
| `linker.rs:333` `"ld"\|"gnu"\|"bfd" => ld.bfd`, `mold.spl find_requested_linker("ld")` | explicit user `SIMPLE_LINKER=ld` override, not a fallback |
| `options.rs:180-196`, `native_binary_options.rs:194-196`, `crt_discovery.spl` `/usr/lib/gcc/...` scans, `-lgcc_s`, `--gcc-toolchain=/usr` | filesystem/library artifacts clang needs on glibc; no gcc binary is executed |
| `stubs.rs:2041+`, `linker.rs:4272+` `Command::new("cc")` | `#[cfg(test)]` only |
| `native_cross.rs` `CrossToolchain` (`cc`, `ar`, `{prefix}-gcc`) | no live caller outside its own module (`pub use` only) |
| `src/compiler_rust/lib/std/src/tooling/compiler/c.spl:33` (`"gcc"` default) | legacy seed std copy, no caller in `src/` or `test/` |
| `cc_detect.rs find_archive_tool` returning `"ar"` | `tools.rs find_archive_tool` already turns a non-LLVM result into `Err(missing_llvm_tool_error("llvm-ar"))` |

## Evidence (this host, `/home/yoon/dev/simple/src/compiler_rust/target/bootstrap/simple run` probe calling `find_c_compiler()`)

| Scenario | Result |
|---|---|
| real PATH (`/home/yoon/dev/llvm/install/bin` first) | `/home/yoon/dev/llvm/install/bin/clang-23` |
| `SIMPLE_CC=gcc` | `[cc-detect] REFUSED C driver 'gcc' -> /usr/bin/aarch64-linux-gnu-gcc-13: it is GCC, not clang. CLAUDE.md Critical Rules: Never use GCC ...` -> `""` |
| `SIMPLE_CC=cc` (symlink to gcc-13) | same refusal naming `/usr/bin/aarch64-linux-gnu-gcc-13` |
| PATH = dir with only `gcc`,`cc` | `[cc-detect] no clang C driver found on PATH (tried: clang, clang-23, ... clang-16); gcc, g++ and bare cc are never used as a fallback ...` -> `""` |

`cargo check -p simple-common --tests` (8G cgroup): clean. `hosted_c_target_guard_spec.spl` 23/23 still green.

## Bootstrap PATH/env (item 4)

`scripts/bootstrap/bootstrap-from-scratch.sh` does NOT source `scripts/setup/llvm-toolchain-env.shs`.
`bootstrap-phase-toolchain.shs:38` takes `${CC:-clang}`, requires the basename to be `clang` or
`clang-NN` (else "Unix phase C compiler must be clang"), resolves it with `command -v`, and exports
`SIMPLE_CC=$CC` (line ~197), so every in-bootstrap `find_c_compiler()` call sees an explicit clang and the
new probe admits it. On this host `command -v clang` -> `/home/yoon/dev/llvm/install/bin/clang` (23.1.0);
`/mnt/data/toolchains/llvm-23-root` does not exist here, so `llvm-toolchain-env.shs` would only add the
`SIMPLE_HOST_LLVM_ROOT` path if set. `stage4-tooling-matrix.shs:135-140` / `stage4-tools-only.sh:38-42`
already die on a gcc linker. No bootstrap script depended on the removed gcc/cc fallbacks.
