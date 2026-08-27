# Clang 23.1 Browser Demo Operator Flow

**Executable spec:** `test/03_system/check/clang_23_1_browser_demo_spec.spl`

## Inspect the installed Clang 23.1 toolchain

Set `LLVM_23_1_PREFIX` to an official 23.1 provider. The resolver admits only
parsed 23.1 Clang, LLD and llvm-ar executables and rejects a missing or mixed
family with the observed path/version.

## Build the browser demo with the admitted compiler

Run `scripts/os/build_browser_demo_client.shs`. The admitted Clang compiles both
the browser source and isolated libc; admitted LLD links it. The output must be
an x86-64 ELF with resolved `getpid`. Tool and output hashes are retained in
`build/os/apps/browser_demo/clang-23.1-evidence.txt`.

## Run the ad-hoc bootstrap smoke

Use the isolated provider and record the candidate Simple binary, command,
version, SHA-256 and no-stub-fallback result. Rust's optional in-process LLVM
backend remains blocked until upstream bindings support LLVM 23; it must not be
represented as migrated by renaming an environment variable.

## Boot SimpleOS and exercise browser content

Run the canonical fullscreen evidence wrapper with the admitted provider and
the provider `build/native_probe/simple`. It stages the exact browser ELF as
`BROWSMF.SMF`, boots QEMU, launches the client and injects keyboard/pointer input.

## Validate retained rendering and input evidence

Require font, baseline, fullscreen, restored and browser frames; byte-identical
staging; browser provenance; and correlated keyboard, pointer and click events.
Software presentation accepts only a strong `solid-material` or
`cpu-composited-material` receipt. Host-GPU presentation additionally accepts
`metal-device-composited-material`. Every receipt remains bound to a rendered
backend, a 64-lowercase-hex material digest, the expected theme and the exact
source manifest; any rejection marker or missing artifact fails the gate.
