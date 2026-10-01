# Explicit LLVM23 native Stage2 linking

## Cause and observed identity

The provisional 893f6de5306 Stage2 transcript put
`/opt/homebrew/Cellar/llvm/23.1.1_1/bin` first in PATH, but its environment
allowlist dropped CC/CXX/LD. The Rust seed therefore selected bare `clang++`.
The captured PATH supports resolution to the installed Clang 23.1.1; process
sampling alone did not capture the executable inode and is not absolute binary
identity proof. The link helper unconditionally emitted `-Wl,-ld_classic`, which
explains observed `/usr/bin/ld` even though outer LD pointed to LLVM's linker.

## Change and compatibility

Darwin Stage2 transcripts now retain CC/CXX/AR/LD/LLVM_CONFIG and the explicit
required LLVM version. Only a lane with SIMPLE_LLVM_REQUIRED_VERSION set
selects `--ld-path=<absolute LD>`, requires the Mach-O `ld64.lld` driver, checks
both selected compiler and linker versions, and retains dead stripping. Missing,
relative, wrong-version, and wrong linker-family pins fail before linking.
Unpinned macOS retains the prior Apple classic linker. Linux, FreeBSD, Windows,
and SoSIX code paths are unchanged; the runtime probe is cfg(macos).

## Verification and resource profile

The focused script extracts the actual Rust command builder and compiles it
with pinned rustc/Clang/LLD. It checks strict arguments, default arguments,
negative pins, and Darwin-only environment forwarding. This is command-builder
coverage, not a full Rust compiler crate test or complete Stage2 run.

A real C++ Mach-O fixture exercises libc++, thread-local storage, a weak default
provider overridden by a force-loaded archive, and dead stripping. Both Apple
classic and LLD 23 binaries print `ready:17:23` and exit 0. Single paired compiler
and link measurements with `/usr/bin/time -l`: classic 0.41 s, 81,674,240 bytes maxRSS;
LLD 0.25 s, 81,690,624 bytes. The 16 KiB RSS difference is measurement-scale; this
fixture supports no compiler throughput claim and is far below 6 GiB.

Logs and fixture: `build/mini_builds/llvm23-native-link/`. The new strict builder
adds two bounded version subprocesses per native link, with no tree scans,
polling, caches, build-sized buffering, or shared mutable state. Version output
is captured in memory; these trusted metadata responses are small. Parent bootstrap
retains output authority. No full Stage2 rerun was started. Full Mach-O runtime
compatibility remains a requirement of the next admitted producer run.

Independent Astra review: no P0/P1 issues for this scoped strict Darwin Stage2
hosted link. Complete Stage2 compatibility remains unverified.
