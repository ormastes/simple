# Linux-to-Windows Stage2 lacks its target compiler driver

Build Binaries run `45205044707`, Windows Stage2 job `137813838631`, spent
about 51 minutes compiling the compiler closure before main-stub compilation
failed to spawn `x86_64-w64-mingw32-clang`. Linux Stage2 succeeded.

The workflow installed clang plus GCC/MinGW sysroot packages and supplied
`SIMPLE_CC=clang`. The canonical target detector reads `CC`, not `SIMPLE_CC`;
without an override it deliberately selects a target-qualified LLVM-MinGW
driver rather than a host clang. The installed packages do not provide that
driver or the LLVM Windows runtime required by the native-project link route.

The CI repair retains Linux cross-production and the Windows GNU target. It
installs the Linux-hosted UCRT distribution from the same LLVM-MinGW release
already used by Windows bootstrap, binds CC/CXX/AR and toolchain discovery to
that distribution, and cross-links a real C main with compiler-rt, libunwind,
and LLD before expensive Simple compilation.

Pin: `llvm-mingw-20260922-ucrt-ubuntu-22.04-x86_64.tar.xz`, SHA-256
`bb7bb7654b33d5aa8712acb837c963b2e0c56352560c76105270a3268c665c21`.
The upstream GitHub release API for `mstorsjo/llvm-mingw` tag `20260922`
publishes this digest. Downloaded bytes must match before extraction.

The preflight establishes driver availability and genuine Windows PE linkage;
it does not claim execution or compiler qualification. Acceptance additionally
requires the normal exact-head Windows Stage2 CI job to finish successfully.
No compiler implementation change, host-tool fallback, GCC runtime substitution,
or manual executable rewriting is involved.
