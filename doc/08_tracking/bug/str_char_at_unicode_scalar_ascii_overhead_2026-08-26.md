# `str_char_at` Unicode correctness has measurable ASCII overhead

## Status

Open optimization follow-up; correctness fix retained.

## Evidence

The former implementation returned `s[idx:idx+1]`, which can create malformed
UTF-8 for any multibyte scalar. The corrected implementation delegates to
`text.char_at(idx)` and passes the focused ASCII and multilingual test (3/3).

On the portable interpreter lane, 21 samples of 4,096 ASCII accesses measured:

| implementation | p50 us | p95 us |
|---|---:|---:|
| unsafe legacy byte slice | 28,785 | 29,436 |
| scalar-correct accessor | 29,568 | 30,760 |

The retained correctness cost is about 2.7% at p50 and 4.5% at p95. A wrapper
that called cached `rt_text_is_ascii` first increased p50 further and was
reverted. Peak RSS remains covered by the enclosing portable performance lane;
this micro-comparison did not isolate per-operation allocation counts.

## Required resolution

Add an explicit byte accessor for byte-oriented callers and benchmark a runtime
intrinsic that uses cached ASCII metadata without an extra FFI round trip. Keep
the scalar reference as the semantic oracle. Acceptance requires matched-host
latency, allocation bytes/count, and peak/steady RSS evidence; no speedup may
trade for a memory regression outside the calibrated gate.
