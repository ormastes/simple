# Text bytes used raw values in tagged word slots

Status: FIXED in source; LLVM and Cranelift core-C native regressions PASS. Rebuilt bootstrap admission pending. Pure-Simple twin has source-equivalence review; its execution is not proved by the core-C probe.

## Failure and producer

The bootstrap runtime's `rt_string_bytes` created ordinary word-backed arrays but stored raw bytes. Generic integer and typed-byte word accessors decode tagged values. A byte divisible by eight was therefore decoded as a different integer: 112 became 14, and 120 became 15. Rust's `rt_string_bytes` already stored tagged words.

The immutable failed producer SHA-256 was `3939f591b869314064b3622378920ebbbb8596eaa9e060751f5c539454ab57b0`. Its `core-c-bootstrap` runtime authority archive SHA-256 was `265a6d3d87a6b81d4d4875ca99ba79c595afb765231bb18afaa875b1b707e3c3`.

Both LLVM and Cranelift eight-module native probes encoded `simple` as bytes 99,50,108,116,68,109,15,108 instead of the known RFC 4648 result `c2ltcGxl`, and returned 1. The complete-octet regression baseline returned 2 at inferred byte 8. These bootstrap diagnostics are retained locally under `build/diagnostic/policy-handoff-20261005`; they are not default test-runner or release admission evidence.

## Repair and regression

`src/runtime/runtime_native.c` and its pure-Simple twin `src/runtime/simple_core/core_string.spl` now store `rt_value_int(byte)` in word slots. Packed byte layouts retain their existing metadata and accessors. The old July raw-word comment described an earlier getter contract and does not apply to current getters; no global integer decoder or array type inference changed.

Tracked executable regression: `test/02_integration/compiler/simple_core_string_bytes_native_probe.spl`. It checks all 256 octets through inferred integer indexing, an integer-array parameter, typed byte-array parameters and fields, the exact Base64 URL encoding of `simple`, and an ASCII 0..127 roundtrip.

Corrected producer SHA-256: `b4d31fc8482f538182308ca35116a0fa57f51fe632df22c3baed7b81ea11699a`. The runtime-path archive remains the preserved authority above; the core-C supplement is freshly compiled from repaired source.

```sh
LLVM_CONFIG=/home/ormastes/.local/toolchains/llvm-23.1.2-apt/usr/lib/llvm-23/bin/llvm-config SIMPLE_NATIVE_BUILD_RUST=1 src/compiler_rust/target/bootstrap/simple native-build --source src/lib --source test/02_integration/compiler --entry-closure --entry test/02_integration/compiler/simple_core_string_bytes_native_probe.spl --backend llvm --runtime-bundle core-c-bootstrap --threads 1 --cache-dir build/diagnostic/policy-handoff-20261005/cache-octets-fixed-llvm --runtime-path .simple/storage/build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority/deps/libsimple_runtime.a -o build/diagnostic/policy-handoff-20261005/octets-fixed-llvm
build/diagnostic/policy-handoff-20261005/octets-fixed-llvm
```

LLVM built eight modules successfully and the executable printed `simple-core-string-bytes: all 256 octets, typed reads and Base64 PASS`, exit 0. This independent byte-provider defect must not be conflated with the full LLVM Stage2 `invalid-policy` failure until the rebuilt bootstrap boundary passes.

Cranelift independently built the same eight-module regression (0.3 s compile, 7.6 s link), printed the same PASS message, and returned 0. Use the command above with `--backend cranelift`, `cache-octets-fixed-cl`, and output `octets-fixed-cl`. Read-only runtime review found no P0/P1 issues in the exact repair and regression.

The exact pure-Simple `core_string.spl` archive was also executed against the C implementation in an isolated paired diagnostic. All 256 octets passed 1,024 boxed/raw assertions, exit 0. The immutable producer was `b4d31fc8`; commands, source and executable hashes are retained in `build/diagnostic/string-twin-20261005/{evidence.md,inputs.sha256,run.log}`. This proves the actual twin's behavior; it does not substitute for protected capsule admission or full bootstrap qualification.
