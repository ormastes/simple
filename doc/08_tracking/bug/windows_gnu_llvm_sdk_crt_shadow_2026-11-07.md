# Windows GNU LLVM SDK library search shadows the selected CRT

- Proposed bug ID: windows_gnu_llvm_sdk_crt_shadow_2026_11_07
- Severity: P1 (blocks fresh Phase1 seed linking).
- Status: implementation integrated; canonical rebuild verification running. Not fixed/admitted.
- Source owner: scripts/bootstrap/bootstrap-from-scratch.sh, Windows GNU mingw_rustflags binding and run_rust_authority_env.
- Source baseline: release/1.0.0 snapshot 65a1117b51f.

## Reproducer and cause

Pinned GNU-host Rust nightly-2026-09-15, target x86_64-pc-windows-gnullvm; LLVM-MinGW 20260922 / Clang23.1.2 C driver and CRT; MSYS2 CLANG64 LLVM23.1.5 SDK. Final simple-driver link failed:

    ld.lld: error: undefined symbol: _MINGW_INSTALL_DEBUG_MATHERR
    referenced by LLVM-MinGW x86_64-w64-mingw32/lib/crt2.o

The selected Clang driver owns crt2.o, but the LLVM dependency's rustc-link-search adds its SDK lib directory before Clang's default CRT paths. Rust's -lmingwex then picks the SDK's different archive. The driver's own libmingwex.a defines the required symbol. A dummy definition would conceal inconsistent CRT selection.

## Exact retained real Cargo evidence

Fixture: build/review/gnu-crt-shadow/fixture (std-only app + local dependency whose build.rs emits the actual CLANG64 SDK library directory). No compiler suite or mocked link success was substituted.

- cargo-shadow.log: cargo build --target x86_64-pc-windows-gnullvm --offline -vv; exit101, exact missing MATHERR symbol.
- cargo-target-flags.log: same real fixture with selected MinGW CRT directory first in native Rust search flags; exit0; emitted executable ran and printed coherent Cargo CRT OK.
- cargo-encoded-spaces.log and encoded-regression.log: extracted proposed production flags/env owners, unit-separated flags, native CRT alias path containing a space, canonical target/LLD arguments and ordinary ambient --cfg; exit0; emitted executable asserted result23 and printed coherent Cargo CRT and ambient flags OK.
- check-evidence.py: canonical token boundaries, explicit encoded ambient precedence and non-GNU hook isolation passed. Explicitly empty encoded flags suppress ordinary ambient flags (separate retained metadata check).
- bash -n and git apply --check passed on private gnu-crt-search-priority.patch.

## Repair and remaining gate

Resolve libmingw32.a from the selected Clang driver; validate CRT archive directory; prepend its native Rust search path for every GNU authority Cargo root. Use CARGO_ENCODED_RUSTFLAGS centrally so paths with spaces remain one argument, preserve canonical/ambient argument semantics, and bind the exact effective encoded flags into Cargo configuration identity. Non-GNU calls remain unchanged.

The integrated scripts-only patch must pass canonical Phase1 seed construction, retain actual compiler/runtime identities and Hello evidence, and then qualify dependent tools. Tiny fixture success proves CRT selection repair, not a successful compiler seed or deployable MCP/LSP/SPipe build. Existing Cargo caches were not deleted; the changed flag identity legitimately selects a new config key.

## Canonical driver-link result — 2026-11-07

The canonical attempt using the integrated CRT priority and GNU/gnullvm configuration completed simple-driver linking with native_process_status=0 and shell_status=0 in 7m02s. Retained Cargo configuration key: 47d5fc48253d. Output size: 39263232 bytes. Compiler SHA256: 740b4095fcd0979c83e49139c818600cdc7701ab7bd1a0fe82c1a479915aebb0.

Receipt: .simple/storage/build/bootstrap/logs/x86_64-pc-windows-gnu/rust-seed-build.log.process.kx8tRB/command.env. Runtime-library construction and generation admission are still running; this result does not claim a qualified phase or tool deployment.

## Reviewed linker ownership and later retained evidence

The CRT query uses the selected `mingw_linker`, preserving the supported independent CC/linker override contract. The permanent checker passed 11/11 contracts, including distinct CC/linker prefixes, encoded paths with spaces, ambient flag precedence and GNU-only forwarding. Retained log: `build/review/integrated-seed-review/override-positive.log`; checker SHA256: `d1e647a55a3a63c73089638593a646c8d9b0b00a9645a33755d0d8e0fb17e0ef`. These green checks were not replayed for landing.

Later producer `cc13b39f1f9cda63643bea759d5410c2d013b95d580035e00722512833103435` compiled and executed a real LLVM/GNU core-C Hello with exits 0/0 and stdout `windows native hello` (retained `build/review/seed-hello-cc13b39f/evidence.sdn`). Its descendant `5de3d616591e6b2d616d66b06f45d88a64b0b1d8351b332b008995aa376efab1` passed the separately retained observed6 canonical frontend controls in both bootstrap modes plus receiver and positional dynload-route controls. Evidence lives under `build/review/phase2-exact5de3-sanity/observed6`; candidate and runtime identities remained stable.

These are historical producer/control observations, not fresh release-base qualification. Phase1 whole tests remain NOT_PROVEN; the descendant remains PROVISIONAL/NONADMITTED because its original construction status was nonzero. No full CLI, Phase3, MCP/LSP deployment or release admission is claimed. This scripts-only landing excludes seed changes, MCP launchers, native worker changes and shared bug database edits.