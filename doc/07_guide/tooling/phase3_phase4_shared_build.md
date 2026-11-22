# Unified Cross-Platform Phase 3 & Phase 4 Build Guide

All desktop, server, and guest hosts (**Linux**, **macOS**, **FreeBSD**, **Windows (Git-Bash/MSYS2)**, and **SimpleOS**) use the **same shared script** for Phase 3 and Phase 4 self-hosted builds:

- **Shared script:** `scripts/bootstrap/build-phase3-phase4.sh`
- **Windows batch launcher (2 configs delegating to the same `.sh` script — `mingw` DEFAULT, `msvc` optional):** `scripts/bootstrap/build-phase3-phase4.bat`
- **Platform/CPU link policy + `native_host_match` check:** `scripts/bootstrap/stage3-native-host-link-policy.sdn` & `scripts/bootstrap/stage3-native-host-link-policy.shs`

Every core bootstrap script carries the top-of-file `PROTECTED BOOTSTRAP SCRIPT — DO NOT MODIFY UNLESS EXPLICITLY REQUESTED BY USER` banner guarded by `sh scripts/check/fast-verify-bootstrap-scripts.shs`.

---

## 0. Default Bootstrap Skips Phase 1 & Phase 2 Once Phase 3+ Exists

In `scripts/bootstrap/bootstrap-from-scratch.sh --bootstrap-receipt=<receipt>`, when a working native pure-Simple Phase 3+ host compiler already exists (`bin/release/<triple>/simple` or `bin/simple` without the Rust-seed banner), **default bootstrap skips Phase 1 (Cargo Rust seed) and Phase 2 (`seed -> stage2`)** and delegates directly to `scripts/bootstrap/build-phase3-phase4.sh` (`P3 -> P4`). Note that `sh scripts/bootstrap/build-phase3-phase4.sh` is the direct interactive/CLI phased entrypoint for Stage 3 & Stage 4, while multi-stage `bootstrap-from-scratch.sh` builds require `--bootstrap-receipt=<receipt>`:

```bash
# Default planner-admitted bootstrap: skips Phase 1 & Phase 2 when Phase 3+ exists, running P3 -> P4 directly
sh scripts/bootstrap/bootstrap-from-scratch.sh --bootstrap-receipt=<receipt>

# Require an existing Phase 3+ compiler without seed fallback
sh scripts/bootstrap/bootstrap-from-scratch.sh --bootstrap-receipt=<receipt> --skip-seed

# Cold rebuild from Phase 1 (Cargo Rust seed) + Phase 2 ONLY when intentionally requested
sh scripts/bootstrap/bootstrap-from-scratch.sh --bootstrap-receipt=<receipt> --from-seed
sh scripts/bootstrap/bootstrap-from-scratch.sh --bootstrap-receipt=<receipt> --cold-bootstrap
# (CI cold-seed matrix uses --full-bootstrap --bootstrap-receipt=<receipt>, or --stop-after-stage2 --produce-stage3-receipt=<reason>)
```

---

## 1. Interactive Phased Build Menu

Running `sh scripts/bootstrap/build-phase3-phase4.sh --menu` (or running interactively in a terminal without `--phase=...`) displays the phased build menu; non-interactive automation passes `--phase=p3a|p3|p4|all`:

```text
============================================================
  Simple Self-Hosted Phased Build (Phase 3 / Phase 4)
  Host: darwin-aarch64 | Target: aarch64-apple-darwin [native_host_match=PASS]
  Windows Config: n/a | P3 Compile: shard
============================================================
  1) Phase 3a only          (P2 -> P3a, shard compile + dynlib/static-primitive link)
  2) Phase 3a + 3b verify   (P2 -> P3a -> P3b + internal linker gate)
  3) Phase 4 only           (P3b -> P4 release + debug-xray + Stage 5 essentials)
  4) Full Phase 3 + Phase 4 (P2 -> P3a -> P3b -> P4 all)
  5) Phase 3 (file-based parallel option: --compile-mode=file)
  6) Phase 3 (phased HIR/MIR shard option: --compile-mode=shard)
  0) Exit
============================================================
```

---

## 2. Shared CLI Options Across Linux, macOS, FreeBSD, Windows, and SimpleOS

```bash
# Phase 3a only (P2/P3 -> P3a, shard compile + dynlib/static-primitive link)
sh scripts/bootstrap/build-phase3-phase4.sh --phase=p3a --compile-mode=shard

# Default Phase 3 (shard / phase build is DEFAULT: SIMPLE_FILE_WORKERS=0, SIMPLE_HIR_SHARDING=1, SIMPLE_MIR_SHARDING=1)
sh scripts/bootstrap/build-phase3-phase4.sh --phase=p3 --compile-mode=shard

# Optional Phase 3 parallel per-file worker pool (--compile-mode=file: SIMPLE_FILE_WORKERS=1)
sh scripts/bootstrap/build-phase3-phase4.sh --phase=p3 --compile-mode=file

# Phase 4 dual-mode build (release `simple` AND debug+XRay `simple-debug` + 4 Stage 5 tools)
sh scripts/bootstrap/build-phase3-phase4.sh --phase=p4

# Full Phase 3a -> Phase 3b -> Phase 4 pipeline
sh scripts/bootstrap/build-phase3-phase4.sh --phase=all --threads=10
```

### Windows Batch Wrapper (`mingw` Default, `msvc` Optional)

`scripts\bootstrap\build-phase3-phase4.bat` locates Git-Bash or MSYS2 `bash.exe` (rejecting the WSL `System32\bash.exe` stub) and forwards all arguments to `scripts/bootstrap/build-phase3-phase4.sh`:

```bat
rem Config 1 (DEFAULT): --win-config=mingw (llvm-mingw clang + ld.lld)
scripts\bootstrap\build-phase3-phase4.bat --phase=p3 --compile-mode=shard

rem Config 2 (Optional): --win-config=msvc (clang-cl)
scripts\bootstrap\build-phase3-phase4.bat --win-config=msvc --phase=p3 --compile-mode=shard

rem Interactive menu on Windows:
scripts\bootstrap\build-phase3-phase4.bat --menu
```

---

## 3. Platform/CPU Link Policy & Mandatory `native_host_match` Tag Check

`scripts/bootstrap/stage3-native-host-link-policy.sdn` (`schema: "simple-stage3-native-host-link-policy-v1"`) and `scripts/bootstrap/stage3-native-host-link-policy.shs` define per-`(platform, cpu)` link profiles (`darwin-aarch64`, `darwin-x86_64`, `linux-x86_64`, `linux-aarch64`, `linux-riscv64`, `freebsd-x86_64`, `freebsd-aarch64`, `windows-x86_64`, `windows-aarch64`, `simpleos-x86_64`, `simpleos-aarch64`, `simpleos-riscv64`):

1. **Mandatory `native_host_match` Tag Check:** Verifies `native_host_match: true` in the SDN profile AND checks `target (platform, cpu) == host (os, arch)`. Any cross-host mismatch fails closed with `STAGE3-E-NATIVE-HOST-MISMATCH`.
2. **Minimal Static Primitive + Shared Unit Link:** Minimizes the `simple` binary to link **only** thin entry + `(platform, cpu)` static primitive archive (`libsimple-primitive-<platform>-<cpu>.a`, `SIMPLE_STAGE3_MINIMAL_STATIC_PRIMITIVES=1`) + dead-stripped primitive C core statically, while linking `lib/libsimple-{std,compiler-common,compiler,app}.dylib` (`.so` / `.dll`) dynamically.
3. **Native-Host-Only Phase 3 Targets (Existing `.dylib` Plugins Still Loadable):** Phase 3 omits `src/plugins` and sets `SIMPLE_STAGE3_BUILD_EXTRA_DYNLIBS=0` so non-native backends (other CPUs, VHDL, GPU/CUDA/Vulkan, Wasm) are **NOT** built during Phase 3 — **but if a `.dylib` already exists on disk, `simple` can load and use it** (`--backend-plugin <existing.dylib>`, `SIMPLE_STAGE3_ALLOW_EXISTING_DYNLIBS=1`).

---

## 4. Phase 4 Dual-Mode Build (`--xray` + Optimized Release) & Stage 5 Essentials

Running `--phase=p4` (or `--phase=all`) builds **both** Phase 4 full-CLI variants in isolated profile namespaces plus the four Stage 5 essential tools:

- **Optimized production binary (`simple`):** `--profile=prod --release --strip`
- **XRay-instrumented debug binary (`simple-debug`):** `--profile=dev --debug --no-strip --xray`
- **Stage 5 essentials:** `simple_test_runner`, `simple_build_runner`, `simple_mcp_server`, and `simple_lsp_mcp_server`

---

## 5. Zero-Compile `--path-check` Alive Verification & Protected Script Guard

Every core bootstrap script carries a top-of-file `PROTECTED BOOTSTRAP SCRIPT — DO NOT MODIFY UNLESS EXPLICITLY REQUESTED BY USER` banner. Run the sub-second verifier to check sealed `.sdn` SHA-256 digests, protected banners, shell syntax, and `check-bootstrap-path-matrix-all.shs` across Unix, Windows, and SimpleOS without running actual compilation:

```bash
# Sub-second verification of sealed SHA-256 digests, protected banners, syntax, and alive path matrix
sh scripts/check/fast-verify-bootstrap-scripts.shs

# Direct alive path probes (no compilation)
sh scripts/bootstrap/build-phase3-phase4.sh --path-check
sh scripts/bootstrap/build-phase3-phase4.sh --path-check --simulate-host=linux-x86_64 --phase=p3 --compile-mode=shard
sh scripts/bootstrap/build-phase3-phase4.sh --path-check --simulate-host=windows-x86_64 --win-config=mingw --phase=all
```

Each active phase emits extensible `PATH_ACTION|...|status=ALIVE` superset records so newly added steps remain forward-compatible with contract tests.

---

## 6. Deprecated Standalone Scripts

Legacy standalone Phase 3/4 scripts (`p3-selfbuild-stage3.shs`, `p3-manual-link-stage3.shs`, `p3-smoke-stage3.shs`, `p3-targeted-stage2-build.shs`, `p3-entry-groups.shs`, etc.) remain in `scripts/bootstrap/` for historical reference, but invoking them directly pauses with migration instructions showing how to run `build-phase3-phase4.sh` (including `--compile-mode=shard` and `--compile-mode=file`) and returns without building.

See also [bootstrap_options.md](bootstrap_options.md), [build.md](../compiler/build.md), and [release_full_bootstrap.md](../infra/release_full_bootstrap.md).
