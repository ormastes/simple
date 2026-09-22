# Phase2 native tool builds selected GNU tools under Git Bash

At source `45fb44e4a7d19732a279225f39ce091eec9b2efe`, the admitted Phase2
compiler snapshot SHA256 was
`8a1aca82c31f7fbf1715b8e2b6e309601f634d5b4a2c82a686d3b96fb3cf5989`.
Read-only evidence is in `D:/w9/build/review/phase2-45f/summary.env` and
`logs/mcp_build.log` / `logs/lsp_build.log`. Both service builds terminalized
FAIL with status 87: the expected executable was absent even though the
compiler returned zero. The main-stub diagnostic selected `gcc` and rejected
`--target=x86_64-w64-windows-gnu`.

The phase matrix inherited its native toolchain. The Rust target owner treats
Windows `MSYSTEM` as GNU unless a target/flavor overrides it, and the C compiler
owner follows that flavor. The existing CL conversion exclusion preserves an
already selected clang-cl `/TC`; it does not select clang-cl or an MSVC target.

The phase command boundary now requires an absolute configured LLVM prefix,
its executable clang-cl 23.1.1, MSVC ABI/flavor/target, and `/TC` on Windows.
Conflicting compiler, ABI, flavor, target, or C-mode settings fail before the
build. Version probing uses the same bounded executor as the matrix. All
environment changes remain in the command subshell. The wrapper selects
CC=clang and CXX=clang++ on Unix-like hosts, preserving their target arguments;
GCC aliases are not an implicit fallback. Non-build commands retain their
previous dispatch. Core source-language and compiler fallback enforcement are
separate changes owned by the compiler lane.

## Focused evidence

`test/01_unit/scripts/bootstrap_phase_windows_toolchain_test.shs` first failed
against a behavior-preserving passthrough boundary with
`FAIL: native build selected ambient compiler` (exit 1). After the fix it passed
(exit 0) using Git Bash and
`LLVM_SYS_231_PREFIX=C:/dev/tool/clang+llvm-23.1.1-x86_64-pc-windows-msvc`.
The test compiles a C-only `.cpp` probe with the real pinned clang-cl, poisons
PATH with forbidden compiler names, rejects incompatible overrides, checks
parent-environment isolation and non-build dispatch, and simulates Linux,
Darwin, FreeBSD and SimpleOS policy dispatch. One intermediate harness failure
from Git Bash converting `-Fo` was resolved with argument conversion disabled
only around the test's direct native compiler call.

This is bounded command-policy and real Windows C-driver evidence, not a
Phase2 matrix pass, service build success, or native Unix execution result.
No full verifier or bootstrap was rerun, and `D:/w9` was not modified.

Review identified that older admitted compilers can consult CXX on Unix.
`bootstrap_phase_unix_toolchain_test.shs` covers both driver bindings, rejects
ambient gcc/g++ overrides, and invokes the selected test drivers with poisoned
GCC candidates on PATH. This remains simulated host-policy evidence.

Remaining integration limits: this boundary does not reconcile a conflicting
`SIMPLE_LLVM_BIN` with the configured prefix, and the effect of an ambient
`_CL_` override on clang-cl C mode was not tested. It does not claim arbitrary
hostile-environment closure or replace the compiler lane's source-language gate.
