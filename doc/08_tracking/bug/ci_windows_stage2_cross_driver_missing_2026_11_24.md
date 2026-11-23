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

## Explicit target runtime ownership

The bootstrap-main runtime selector prioritizes `libsimple_native_all.a` and
requires eight concrete runtime owners, including `rt_native_build`. Its last
resort Cargo invocation builds a host archive without a cross target. Restoring
a Linux Cargo cache does not establish Windows runtime authority.

The Windows seed job therefore builds native-all for its gnullvm target in a
separate canonical feature invocation, after uploading the original seed and
its matching runtime. The cross job downloads this same-source archive, checks
its hash, requires every member to be x86_64 COFF (including COFF import members),
and checks the selector's actual required exports. It passes the directory as
an explicit runtime path. Compiler backfill is a Stage4 owner and is not selected
by this bootstrap-main route; its generated core-C mutex/provider supplement
remains owned by NativeProjectBuilder and the selected target compiler.

A tiny `bootstrap_main.spl` is cross-linked through that actual owner before the
full closure. Both preflight and Stage2 must report the retained archive as their
runtime source. Native object staging and object caches are retained so a later
link failure can be diagnosed without recompiling the unchanged closure.

## Target COFF intermediate closure

Run 45225760378 admitted the matching Windows archive and compiled the tiny
preflight module (1 compiled, 0 failed), then PE LLD rejected `-r` while building
the Stage4 runtime capsule. The C driver was correctly target-qualified; this
was an intermediate linker capability mismatch, not a missing CRT or archive.

Windows GNU intermediate closures use GNU PE BFD with an explicitly validated
machine emulation (`i386pep` for x86_64, `i386pe` for x86). Selection requires a
GNU ld identity and advertised emulation; missing tools fail closed. ELF and
Mach-O paths retain their prior commands. Final PE links remain pinned UCRT
Clang/LLD. Root cardinality, unresolved-runtime, tombstone, localization and
archive-symbol checks remain mandatory. BFD-produced COFF weak fallbacks use
the existing repair before those checks.

The focused `scripts/check/check-coff-partial-link.py` exercises the actual
production selector, the failing LLD negative control, rooted COFF extraction,
and Clang/LLD final PE linking. It can additionally reuse the retained real
core-C archive. Its result describes link capability, not foreign execution
or a complete Stage2 qualification. Full cross Stage2 remains required.
