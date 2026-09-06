# Interpreter-mode watchdog timeout on heavy crypto/PQC KAT specs (7 specs)

- **Date:** 2026-07-20
- **Area:** SSpec test-runner / interpreter performance, exercised via 7
  crypto specs whose primitives are CPU-heavy (bcrypt Blowfish key
  schedule, Ed448 448-bit field arithmetic, ML-DSA-65/87 lattice/NTT
  keygen, RSA-PSS-SHA256 modular exponentiation, SLH-DSA-128s/192s/256s
  hash-tree signing).
- **Severity:** medium — these specs cannot complete in interpreter mode
  within the test-runner's internal watchdog (~60s) or the outer harness
  timeout (90s); correctness of the underlying primitives is UNVERIFIED,
  not merely slow.
- **Status:** OPEN. This is not one of the guide's literal ENV categories
  (no missing tool/socket/GPU/network, not gui/webgpu/webgl/wm/ml/simpleos)
  — filing as a tracked bug/perf-gap rather than silently skipping, per
  instruction to not bare-skip ambiguous cases.

## Symptom

All 7 commands below were run exactly as:

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test <spec> --no-session-daemon
```

| Spec | Result | Duration | Notes |
|---|---|---|---|
| `test/unit/lib/crypto/bcrypt_kat_spec.spl` | FAIL, no summary for the KAT describe block | 60248ms | Spec's own header comment (lines 9-18) documents: cost=4 bcrypt performs "~33k Blowfish encryptions in pure [Simple]... likely exceeds the 60s watchdog in interpreter mode"; KAT block explicitly labeled "pending native fast-path" / "pending FR bcrypt_native_runtime_helpers_2026-05-02" |
| `test/unit/lib/crypto/ed448_rfc8032_kat_spec.spl` | FAIL "no examples executed" | 63305ms | Spec header (lines 15-17) acknowledges "interpreter-mode KAT throughput is dominated by point-scalar-mul"; vectors already trimmed for this reason |
| `test/unit/lib/crypto/ml_dsa_65_spec.spl` | FAIL after 15 examples pass (0 failures) across 5 describe blocks, then hang | 67836ms | Fails immediately after "ml_dsa_keygen_65 produces pk of size 1952 bytes" passes; no semantic/resolution error |
| `test/unit/lib/crypto/ml_dsa_87_kat_spec.spl` | FAIL, no examples-passed line at all | 68059ms | ML-DSA-87 is the largest FIPS 204 param set — even heavier than ML-DSA-65 |
| `test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl` | FAIL "no examples executed" | 64924ms | Filename itself is `..._slow_spec.spl` — self-documented as a known-slow RSA test |
| `test/unit/lib/crypto/slh_dsa_128s_spec.spl` | FAIL, no examples-passed line | 68037ms | SLH-DSA/SPHINCS+ hash-tree signing |
| `test/unit/lib/crypto/slh_dsa_192s_256s_spec.spl` | FAIL, process killed by the **outer 90s `timeout`** with zero test-summary output | >90000ms (hard-killed) | SLH-DSA-192s/256s trees are larger than 128s — harder failure than the other 6 (no graceful internal-watchdog summary at all) |

## Root-cause hypothesis

The pure-Simple interpreter is too slow to complete these specific
CPU-heavy cryptographic primitives (Blowfish×33k, 448-bit field
arithmetic, lattice/NTT operations, RSA modexp, SPHINCS+ hash trees)
within either the test-runner's internal ~60s per-spec watchdog or the
outer 90s harness timeout used for this triage pass. Several of the
affected specs (bcrypt, ed448, rsa_pss "_slow_") explicitly self-document
this expectation in their own header comments — this is a known,
pre-existing performance ceiling, not a new regression, but it currently
has no dedicated tracking doc and no native/compiled fast-path to route
around it (bcrypt cites `FR bcrypt_native_runtime_helpers_2026-05-02` as
the pending fix vector).

## What NOT to do

- Do not raise the harness timeout to "fix" this — that papers over
  unverified correctness rather than addressing it, and these specs may
  still exceed any practical timeout in interpreter mode.
- Do not weaken/skip assertions in these specs to force a pass.
- Do not attempt a Rust-seed-level interpreter perf fix here (out of
  scope for a triage pass; needs a rebuild + dedicated perf work,
  possibly the native/compiled-mode fast-path already referenced by the
  bcrypt spec).

## Suggested follow-up (not implemented here)

Route these specs through compiled/native execution mode instead of the
interpreter (several `test/unit/lib/crypto/*` specs already carry
"assertions only fire under compiled/native mode" notes for similar
reasons — see `pem_rfc7468_kat_spec.spl` and `sha2_nist_vectors_spec.spl`
headers), or land the native fast-path helpers already tracked for bcrypt.

## Affected specs

- `test/unit/lib/crypto/bcrypt_kat_spec.spl`
- `test/unit/lib/crypto/ed448_rfc8032_kat_spec.spl`
- `test/unit/lib/crypto/ml_dsa_65_spec.spl`
- `test/unit/lib/crypto/ml_dsa_87_kat_spec.spl`
- `test/unit/lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl`
- `test/unit/lib/crypto/slh_dsa_128s_spec.spl`
- `test/unit/lib/crypto/slh_dsa_192s_256s_spec.spl`
