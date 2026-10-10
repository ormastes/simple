# Native text-to-bytes returns empty for nonempty text (2026-10-10)

Status: OPEN runtime ABI defect; sanctioned Simple facade has a guarded correctness fallback.

## Reproduction

Use pure-Simple Stage 2 candidate SHA-256 `c535be7321e80a4857413fa1c690008b3172b157e87eac8a860edd98c6772082` to native-build `test/fixtures/compiler/sha256_text_native_probe.spl` with `--backend llvm --runtime-bundle core-c-bootstrap --source src/lib --entry-closure`. The six-module pre-fix executable reported `source-len=8 first=112 encoded-len=0` for `"producer"`. The pure Simple and accelerated SHA-256 functions both returned the correct digest `d1990f97a1f4fe7b8e86da8c03c9dd3f7d536c14aa4a6f9eedab07f34cd961b0` on an explicit byte array; `sha256_text("producer")` returned the empty-input digest.

Logs: `build/mini_builds/item6_sha_text_native_{probe,diagnostic,fallback}_20261010/`. The minimal post-fix executable passes ASCII, two-byte UTF-8, alias conversion, byte-hash parity, and text hash.

## Current mitigation

`src/lib/common/text_bytes.spl` retains the runtime conversion as its fast path. When nonempty text unexpectedly produces an empty array, it copies the verified `text.byte_at` view into one sized `[u8]` buffer. Both sanctioned wrapper names use that path. This restores correctness for callers using the facade and leaves the working runtime path unchanged.

## Remaining work

Isolate whether `rt_text_to_bytes` receives the wrong text representation or the linked core-C implementation decodes it incorrectly; fix the compiler/runtime ABI at its owner. Direct `rt_text_to_bytes` callers do not use this facade. Measure fallback time and peak RSS on realistic input against a correct native conversion before treating it as a performance optimization. Re-run the full package index CAS fixture and publication/readback only in a fresh bounded verification cycle. No Item 6 completion or release evidence is claimed here.
