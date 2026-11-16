# Feature Expert — Cross-Compile Lane

## Role

Own process knowledge for cross-compiling the Simple compiler (lint and
test-runner artifacts) from WSL/Linux to Windows, FreeBSD, Linux
riscv64/i686/armv7/aarch64, and SimpleOS.

## Pipeline Links

- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)

## Feature Links

- Guide (matrix, recipe, tags): `doc/07_guide/infra/toolchain/cross_compile_status_2026-11-15.md`
- Bootstrap env scrub: `scripts/bootstrap/bootstrap-from-scratch.sh` ~2589-2611
- HIR sharding switch: `src/app/cli/native_build_main.spl:969`

## Load-bearing facts

Tags: [V] verified, [U] unverified. Landed fixes are verification-pending.

- [V] Smoke links (clang + `file` only) passed for PE32+ x86-64/Aarch64, ELF
  FreeBSD x86-64/aarch64, ELF RISC-V, ELF 80386, ELF ARM. No lint/test-runner
  cross artifact exists for any target yet.
- [V] Bootstrap scrubs the env; only `SIMPLE_BUILD_MEMORY_RESERVE_BYTES=2147483648`
  survives. Run the self-hosted phase-2 builder (WSL `~/xc/simple-p2`) with it.
- [U] After a seed rebuild use `--invalidate-cache=stage2`.
- Matrix: `sh scripts/check/check-cross-compile-matrix.shs [--targets a,b]
  [--artifacts lint,test] [--builder P] [--min-free-gb 8] [--run] [--dry-run]
  [--selftest] [--list]`. Linux host only. Preflight (clang, ld.lld,
  llvm-readelf, rustup target, sysroots, llvm-mingw, compiler-rt, qemu-user)
  gives ERROR rows with fix hints; Linux rv64/i686/armv7 also run
  `check-linux-cross-no-libgcc.shs`. One build at a time,
  `SIMPLE_CACHE_SCOPE=xc-<target>`, artifact class/machine via
  `file`+`llvm-readelf`/`llvm-readobj`, `--run` via qemu-user only (no wine).
  Results `build/cross-matrix/results.tsv` + markdown table, verdict last.
  Extra targets (NVMe FW bare-metal lane): `XC_MATRIX_EXTRA_TARGETS=<tsv>`.
  Bare-metal rows are BLOCKED by default (no hosted runtime for lint/test).
- Per-target status and toolchain setup: the guide's "Matrix script" and
  "Toolchain setup" sections. [V] 2026-11-16: selftest 22/22 and dry-run
  preflight ok for all 12 hosted targets in WSL; no real build yet.
- [U] `SIMPLE_HIR_SHARDING=0` workaround; should be unneeded after #9427.
- Push gates: `MUST_CHECK_PUSH_BUDGET_S=600` on loaded hosts; never `--no-verify`.
- [U] Landed, verification-pending: #9373, #9388, #9391, #9393, #9395, #9424,
  #9427 (details in the guide).
- Open: llc-18 `expected 'ptr'` on ptrtoint (fix lane running); Linux cross
  uses `libgcc-13-dev-*-cross`, conflicting with no-GCC policy (use
  compiler-rt); riscv32 has no sysroot; no 32-bit SimpleOS triples; the
  llvm-mingw installer only fetches the Windows-hosted zip.
- Pre-existing, not regressions: `hir_cache_semantic_closure_digest_spec` 2/6
  on base [V]; `hir_closure_digest_interface_keyed_spec` missing
  `hir_cache_iface_fallback_count` [V]; `llvm_pointer_return_null_spec` removed
  `translate_call` [U].
