# SIMD Runtime Performance Evidence

Date: 2026-04-30
Scope: remaining SIMD tranche runtime perf evidence for text/scan, UTF-8, AES, and primitive sort

STATUS: WARN

## Environment

- host OS: `Linux 6.8.0-107-generic`
- host arch: `x86_64`
- detected runtime tier: `x86_64_avx2`
- local limitation: no AArch64/NEON host was available in this run, so checked measurements below are AVX2-only

## Commands

Bench targets compiled successfully:

```bash
CARGO_TARGET_DIR=/tmp/simple-simd-remains cargo bench \
  --manifest-path src/compiler_rust/runtime/Cargo.toml \
  --features bench-internals \
  --bench primitive_sort_bench \
  --bench simd_text_utf8_aes_bench \
  --no-run
```

Focused runtime tests passed:

```bash
CARGO_TARGET_DIR=/tmp/simple-simd-remains cargo test \
  --manifest-path src/compiler_rust/runtime/Cargo.toml \
  primitive_sort \
  --features bench-internals \
  -- --nocapture
```

Measured timings came from a temporary release-mode Rust probe that imported the runtime bench-support entrypoints and compared `SimdTier::Scalar` against the detected host tier over the same fixtures used by the checked bench codepaths.

## Results

Scalar vs detected AVX2 tier, average milliseconds per operation:

| Metric | Scalar ms | AVX2 ms | Speedup |
|---|---:|---:|---:|
| `text_find` | 0.0010 | 0.0001 | 11.958x |
| `text_rfind` | 0.0000 | 0.0000 | 0.546x |
| `text_split` | 5.8401 | 0.2313 | 25.248x |
| `utf8_count` | 0.2919 | 0.3077 | 0.949x |
| `utf8_validate` | 0.4092 | 0.3757 | 1.089x |
| `utf8_find_invalid` | 0.4227 | 0.4127 | 1.024x |
| `aes_encrypt` | 0.8254 | 0.0371 | 22.251x |
| `aes_decrypt` | 2.4441 | 0.0405 | 60.278x |
| `sort_int` (65,536 elems) | 2.8375 | 2.2911 | 1.238x |
| `sort_float` (65,536 elems) | 2.1877 | 2.2131 | 0.989x |
| `sort_byte` (65,536 elems) | 1.0926 | 0.2168 | 5.039x |

Additional sort crossover probe:

| Metric | Scalar packed ms | Host-tier ms | Speedup |
|---|---:|---:|---:|
| `sort_int` (1,048,576 elems) | 31.6596 | 35.6403 | 0.888x |
| `sort_float` (1,048,576 elems) | 34.6586 | 32.8805 | 1.054x |

## Interpretation

- Text/scan:
  - `find` and especially `split` show clear AVX2 wins.
  - `rfind` does not show a local win on this fixture.
- UTF-8:
  - `validate` and `find_invalid` are slight wins.
  - `count_codepoints` is slightly slower than scalar on this host.
- AES:
  - block encrypt/decrypt show strong AVX2 wins with expanded-key reuse.
- Primitive sort:
  - byte-like arrays show a clear win from the SIMD-tier histogram path.
  - the original AVX2 int/float radix path was regressing due to key materialization plus scalar radix passes, so the current runtime now routes int/float host-tier sorts back to the packed scalar primitive path by default.
  - with that reclassification in place, local host-tier int/float timings are now near scalar and no longer force the prior large regression.

## Conclusion

This tranche now has:

- checked runtime bench targets for text/UTF-8/AES and primitive sort
- checked AVX2 evidence for text, UTF-8, AES, and primitive sort
- checked startup/RSS evidence in `doc/09_report/verify/simd_startup_rss_evidence_2026-04-30.md`

What remains open from a strict performance-acceptance perspective:

- NEON runtime evidence is still uncollected on a real AArch64 host
- primitive int/float do not yet have a winning non-scalar kernel on this x86_64 AVX2 host; they are currently reclassified to scalar fallback to avoid regression
- `utf8_count_codepoints` and `text_rfind` also do not currently show a local speedup on this fixture
