# LLVM Host/Native toolchains select x86_64 on ARM64 macOS

- Severity: P1 (wrong architecture linker selection).
- Status: source fix implemented; runtime verification blocked.
- Scope: pure-Simple LLVM toolchain descriptors; no bootstrap or deployment.

`toolchain_for_target` detected the host architecture but its `Host` and
`Native` enum cases fell through to `toolchain_x86_64_native(os)`. On Apple
Silicon, that selected `x86_64-apple-darwin` and `-arch x86_64` even though the
host LLVM emission target is AArch64. This could reject ARM64 objects or link
the wrong architecture when implicit host toolchains are requested.

The selector now dispatches both aliases through `toolchain_for_host`, which
uses the existing architecture descriptors. Known aliases retain their ABI
support decisions; unknown host architectures return an unsupported descriptor.
Explicit target selection is unchanged.

Regression: `test/01_unit/compiler/backend/llvm_host_toolchain_spec.spl` covers
both Apple Silicon names, Intel aliases, native Linux x86/RISC-V selection,
unsupported ARM/RV32/Windows ARM64 hosts, unknown hosts, and both public aliases.

## Evidence and limits

- `git diff --check`: PASS.
- `sh scripts/audit/direct-env-runtime-guard.shs --working`: PASS.
- Attempted focused spec using the designated release path
  `/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple`:
  exit 139 during runner setup, before assertions.
- A subsequent direct source probe revealed that this binary identifies itself
  as a Rust bootstrap seed. It was immediately interrupted (130); no result
  from that runtime is accepted as pure-Simple verification.
- Actual release-path SHA-256:
  `2a59a9cbc17e7e078b2b4dbb44bad7f865a0aa201cbd21405059b412c6c033ba`.
  The adjacent compiler receipt instead names
  `1860830a88ac901b3a608efe428ed1d70c18eaa23bc81fbfeb9a8c757afc6164`.
  This stale receipt cannot admit the binary.
- Focused executable verification and the shared compiler/lib/MCP gates remain
  pending an admitted pure-Simple runtime. No full bootstrap was started.

## Admitted Stage 2 probe

The pure-Simple Stage 2 binary is
`/Users/ormastes/simple/.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple`,
SHA-256 `e1c0f79a7f0bc9b42df99b1219293e9c3852742a24843e07f96e81d5dcbcd81a`.
Its adjacent `stage2-provenance.receipt` and `stage2-sanity.receipt` agree on
that hash and admit pure-Simple provenance. Their referenced `admission.env`
hash also matches `3fb0e91da5ded08eaabdae050a70fc930bea35e7f4a2d8dc31546fcd756f00e8`.
The supported commands are `compile` and `native-build`; general test/run
commands are not admitted. A native-build probe imports the real changed module,
checks the ARM64 descriptor/flags, and checks public Host and Native dispatch.
All probe artifacts and cache are under the lane's `build/llvm-host-probe/`.

Probe fixture: `test/fixtures/compiler/llvm_host_toolchain_macos_arm64.spl`.
Reproduction (from this worktree, with the admitted Stage 2 path above):

```sh
SIMPLE_LIB=src SIMPLE_CACHE_DIR=build/llvm-host-probe/cache \
SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_PACKAGE_INDEX_COLD_INIT=1 \
<stage2> native-build test/fixtures/compiler/llvm_host_toolchain_macos_arm64.spl \
  --output build/llvm-host-probe/probe
```

The recorded run used an identical fixture copy at `build/llvm-host-probe/main.spl`.
Without explicit cold initialization, admission stopped with
`scv-authority-missing`. With cold initialization, source closure resolved 121
files, then HIR lowering failed in existing dependencies, including
`target_presets.spl: unresolved type: BackendCompileOptions`. Exit status: 1.
No executable was produced and no probe assertions ran. The compile log remains
in the isolated lane at `build/llvm-host-probe/native-build-cold.log`.
This is a source fix with pending runtime acceptance, not a verify PASS.
