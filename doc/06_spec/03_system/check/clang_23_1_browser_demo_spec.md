# Clang 23.1 Browser Demo Operator Flow

**Executable spec:** `test/03_system/check/clang_23_1_browser_demo_spec.spl`

## Inspect the installed Clang 23.1 toolchain

Set `LLVM_23_1_PREFIX` to an official 23.1 provider. The resolver admits only
one canonical provider prefix containing all nine required executables:
`clang`, `ld.lld`, `llc`, `opt`, `llvm-ar`, `llvm-nm`, `llvm-objdump`,
`llvm-objcopy`, and `llvm-config`. The provider validates every tool as 23.1.0,
checks `llvm-config --prefix` and `--bindir`, and emits canonical handoff
metadata through `SIMPLE_LLVM_PREFIX`, `SIMPLE_CLANG`, `SIMPLE_LINKER`,
`SIMPLE_LLC`, `SIMPLE_OPT`, `SIMPLE_AR`, `SIMPLE_NM`, `SIMPLE_OBJDUMP`, and
`SIMPLE_OBJCOPY` (with `LLVM_CONFIG` for the upstream configuration tool).
Missing, mixed, or falsely labeled families fail closed.

## Build the browser demo with the admitted compiler

Run `scripts/os/build_browser_demo_client.shs`. The admitted Clang compiles both
the browser source and isolated libc; admitted LLD links it. The output must be
an x86-64 ELF with resolved `getpid`. Tool and output hashes are retained in
`build/os/apps/browser_demo/clang-23.1-evidence.txt`. This client build consumes
the compiler/linker/archiver subset of the same nine-tool provider; it does not
create a second or partially admitted toolchain.

## Run the ad-hoc bootstrap smoke

Produce a current-source full Stage4 CLI and retain its adjacent provenance
sidecar. Admission requires `artifact_kind=pure-simple-full-cli`, the exact
candidate/source/producer/parent hashes, the Stage4 build log, and a hashed
essential-tools log whose completed gate is `stage4-essential-tools-smoke`.
Stage2, Stage3, `native_probe/simple`, and Rust's optional in-process LLVM lane
are diagnostic/provider artifacts only; none satisfies this production gate.

## Boot SimpleOS and exercise browser content

Run the canonical fullscreen evidence wrapper with the admitted nine-tool
provider and full Stage4 CLI. Production selection is
`SIMPLEOS_WM_NATIVE_BACKEND=llvm`; the build exports the canonical `SIMPLE_*`
tool paths, sets `SIMPLE_BOOTSTRAP=0`, retains
`SIMPLE_NATIVE_BUILD_LINKER_SCRIPT`, and uses
`build/simpleos_wm_fullscreen_evidence/native-cache/llvm`. Explicit
`SIMPLEOS_WM_NATIVE_BACKEND=cranelift` remains diagnostic-only and must never be
reported as LLVM 23.1 migration evidence. The wrapper stages the exact browser
ELF as `BROWSMF.SMF`, boots QEMU, launches it, and injects keyboard/pointer input.

## Validate retained rendering and input evidence

Require font, baseline, fullscreen, restored and browser frames; byte-identical
staging; browser provenance; and correlated keyboard, pointer and click events.
The admitted kernel record must agree with the selected `llvm` backend,
backend-scoped cache, `simple_bootstrap=0`, nine-tool identity, and Stage4
provenance hash; changing any field forces a rebuild instead of cache promotion.
Software presentation accepts only a strong `solid-material` or
`cpu-composited-material` receipt. Host-GPU presentation additionally accepts
`metal-device-composited-material`. Every receipt remains bound to a rendered
backend, a 64-lowercase-hex material digest, the expected theme and the exact
source manifest; any rejection marker or missing artifact fails the gate.
