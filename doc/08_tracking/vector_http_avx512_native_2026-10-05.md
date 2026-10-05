# Native HTTP byte/CRLF vector provider evidence

Base: `3b9f3d704b80d937128918228501ca8faff56046`. Isolated implementation;
no root compiler, Phase2 runtime authority, or app cache was modified.

## Contract and implementation

The optional `SIMPLE_VECTOR_ENABLE_HTTP_AVX512` build extends the existing
provider with opcode 3 / capability 4 (find byte) and opcode 4 / capability 8
(find CRLF). The canonical 64-byte request / 24-byte response and digest
`f16901349e16de8bb16f0769f492488fff27d0d0bd3b5f15c20b20b25f060600`
remain unchanged. The Simple contract owner confirmed: only the left borrowed
span is used; right/output fields are zero; argument is a byte for op3 or zero
for op4. Success returns zero bytes_written and the first relative index or -1.
Empty spans require address zero. Inputs are borrowed only during the call.

`bitmap_provider.c` remains compiled for baseline x86-64. HTTP admission
requires existing AVX512F + OS XSTATE checks and CPUID leaf7 EBX bit30
(AVX512BW). Bitmap admission still requires only AVX512F. Query grants only
compiled operation bits; CPU availability is checked on apply, so a valid
capability can return FEATURE_UNAVAILABLE without issuing optional instructions.
Bitmap-only builds still accept just capability bits 1/2 and link without the
new kernel. No global AVX512 compiler flag is used.

`http_avx512.c` is a separate target-attributed AVX512F/BW translation unit.
Byte search compares 64 bytes at a time. CRLF compares adjacent 64-byte loads
only with at least 65 bytes remaining; this detects positions 63/64 without
reading beyond the borrowed span. Remaining candidate positions use bounded
scalar tails. No masked speculative read outside the span is needed. Native
loop counts use the existing provider diagnostic counter.

## Actual execution

Command on the existing x86-64 WSL host:

```sh
CLANG=/usr/local/bin/clang sh scripts/check/check-vector-http-avx512.shs \
    /var/tmp/item5-http-avx512-provider-20261005
```

- Native: **576 differential cases PASS**, 495 actual HTTP vector iterations.
- Forced-no-BW build: **576 refusal cases PASS**, zero HTTP vector iterations;
  the independent 16-word bitmap AND still executes successfully using F.
- Cases include empty/one-byte inputs, high-byte and NUL needles, absent/final
  matches, offsets 0/1/7, 63/64 and 127/128 CRLF, final lone CR, and 16 lengths
  through 257. Scalar oracle results match; input bytes and response canaries
  remain intact. Offset zero ends at a PROT_NONE page to catch overreads.
- Invalid needle, unused fields, overflowing span address, over-limit length,
  invalid CRLF argument, unknown opcode and denied HTTP capability are rejected.
- Objdump confirms no ZMM/mask instructions in the baseline dispatcher and
  actual byte-vector comparisons in the target kernel. Bitmap-only baseline
  compilation also passed independently with HTTP disabled.
- Enforced watchdog: 524288 KiB host RSS / 60 seconds per execution. Exit 77
  means unsupported, never PASS. Logs, identities, source/artifact hashes and
  receipts are retained in the output directory above.

| Artifact | SHA-256 |
|---|---|
| Native provider | `717fbc0792395bcc28cb3c02cb5403f53be7c831616cf3f73d9064f31b3599f0` |
| Forced-no-BW provider | `1ff927c70ecbfb2d0301314f3d38610a3627180928a2d7bc93708d737aa9786a` |
| Native harness | `1188cd7260094b4d6ae15066cc94148643accb5ec1b24e1742d1aee4660b9e80` |
| HTTP kernel source | `734048e24abba4b01d3950b03c38b63b758459f40a91570267aa0e3f2e8cf0bf` |
| Baseline provider source | `b5dada539b5ba7de230d314a1f5bee87380025384bf31a0d1a878ed0d4c337b8` |

## Qualification limits

This is actual native dlopen/provider execution, not synthetic kernel results.
It does not qualify Simple loader session ownership, HTTP server callsites,
end-to-end requests, other ISA backends, maximum-size performance or speedup.
Production provider identity is derived from source; this harness does not
claim host registry authentication or device image attestation. Runtime feature
refusal is tested through a build override; no physical F-only host was used.
The hardware script is registered in `scripts/check/guard_wiring_optout.txt`
as a manual hardware lane rather than an unconditional general-host CI gate.
No Simple compiler/test job ran in this lane.
