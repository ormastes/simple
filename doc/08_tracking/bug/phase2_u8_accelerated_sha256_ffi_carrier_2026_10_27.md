# Pinned Phase 2 byte carrier is rejected by accelerated SHA256 FFI

- Canonical ID: `phase2_u8_accelerated_sha256_ffi_carrier_2026_10_27`
- Status: open; an active source workaround is not a compiler/provider fix.
- Owner: DevHub completion / compiler-runtime owners.
- Created: 2026-10-27.
- Producer: existing P2 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`; no compiler rebuild.
- Source: `src/app/devhub/adapter_minio.spl`.
- Regression: `test/fixtures/devhub/native_minio_binary_put/main.spl`.

Native binary upload failed with an invalid array handle before any loopback request. The accelerated u8 SHA256 boundary is incompatible with this producer. The workaround copies octets by index into the established i64 SHA256 engine without changing the public byte contract.

## Evidence

Initial native compile0 run1 artifact3adb13de091efe809b6a571ced270f697ee30de9d36d33939692a758dcbaaa8d; independent server observed zero requests. Final typed-carrier transport qualification is recorded in the parent verification report and is not assumed here.

## Removal condition

Retire after this deployed producer and linked crypto provider pass exact octets 0,128,255 plus empty, Unicode byte sequences and independent SHA256 goldens through the accelerated ABI. Keep the byte-exact upload and SigV4 oracle.

The standard SSpec suite, all runtime-family combinations and any claim not explicitly tied to an actual artifact remain unqualified. Record the workaround commit in the canonical BugDatabase investigation log after integration; never retire it from a source-only review.

**Revalidated 2026-11-02: still plausible because open; an active source workaround is not a compiler/provider fix; no merged fix commit with a passing regression is cited in this doc.**

## Triage 2026-11-03 (lane s3g2)

Not reproducible from source: both providers already accept packed and boxed [u8] (`rt_tls13_sha256`, `src/runtime/runtime_native.c:10039` via `rt_core_as_registered_array`; Rust twin `value/sffi/hash/sha256.rs:154`), and `sha256_u8_fast_hex` falls back to pure-Simple on a non-32-byte result. "invalid array handle" is thrown by the pinned P2 producer's array-handle check on the typed-carrier argument, observable only in a native run of that producer. Concrete blocker: needs the native fixture run, no static defect to patch. Workaround kept.

Added regression spec `test/01_unit/lib/common/crypto/sha256_u8_accelerated_carrier_spec.spl` (octets 0,128,255 + empty, independent goldens; passes interpreted).

Stage3 verify: native-build `test/fixtures/devhub/native_minio_binary_put/main.spl` and the spec with a current producer; if both pass, delete the copy loop in `_minio_binary_payload_hash` and call `sha256_u8_fast_hex`.
