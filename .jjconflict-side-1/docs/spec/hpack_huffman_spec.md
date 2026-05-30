# HPACK Huffman Correctness and Decode/Encode Coverage

Comprehensive tests for `src/lib/nogc_async_mut/http/h2/hpack_huffman.spl`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #HTTP2-HUFFMAN-001 |
| Category | Stdlib / HTTP/2 / HPACK Huffman |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/unit/lib/nogc_async_mut/http/h2/hpack_huffman_spec.spl` |
| Updated | 2026-05-27 |
| Generator | `simple spipe-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Comprehensive tests for `src/lib/nogc_async_mut/http/h2/hpack_huffman.spl`.
Covers round-trip correctness, RFC 7541 Appendix B/C.4 test vectors,
edge cases (empty, single char, all-padding, max-length), error handling
(truncated/invalid sequences), padding validation, and compression ratio.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 2 |
| Logs | 5 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/unit/lib/nogc_async_mut/http/h2/hpack_huffman/result.json` |
| `summary.txt` | Text artifact | `build/test-artifacts/unit/lib/nogc_async_mut/http/h2/hpack_huffman/summary.txt` |

### Logs

| Item | Kind | Path |
|------|------|------|
| `combined.log` | Log file | `build/test-artifacts/unit/lib/nogc_async_mut/http/h2/hpack_huffman/combined.log` |
| `output.log` | Log file | `build/test-artifacts/unit/lib/nogc_async_mut/http/h2/hpack_huffman/output.log` |
| `run.log` | Log file | `build/test-artifacts/unit/lib/nogc_async_mut/http/h2/hpack_huffman/run.log` |
| `stderr.log` | Log file | `build/test-artifacts/unit/lib/nogc_async_mut/http/h2/hpack_huffman/stderr.log` |
| `stdout.log` | Log file | `build/test-artifacts/unit/lib/nogc_async_mut/http/h2/hpack_huffman/stdout.log` |

## Scenarios

- encodes 'www.example.com' to RFC C.4.1 bytes
- encodes 'no-cache' to RFC C.4.2 bytes
- encodes 'custom-key' to RFC C.4.3 bytes
- encodes 'custom-value' to RFC C.4.3 bytes
- encodes empty input to empty output
- encodes single byte 0x61 ('a') with EOS padding
- encodes single byte 0x30 ('0') correctly
- padding bits are all 1s (EOS prefix)
- decodes 'www.example.com' (C.4.1) correctly
- decodes 'no-cache' (C.4.2) correctly
- decodes 'custom-key' (C.4.3) correctly
- decodes 'custom-value' (C.4.3) correctly
- decodes empty input to empty output
- decodes with zero bit_count returns empty
- truncated input returns partial decode (not crash)
- single all-1s byte (pure padding) decodes to empty
- round-trips empty input
- round-trips single byte 'a' (0x61)
- round-trips 'content-type'
- round-trips 'GET'
- round-trips '/index.html'
- round-trips 'www.example.com'
- round-trips 'no-cache'
- round-trips 100-byte repeating payload
- round-trips 256-byte indexed payload (all symbols 0x00-0xff)
- encoded_length matches actual encode output length
- encoded_length of empty input is zero
- encoded_length of single 'a' is 1
- typical HTTP text compresses (output <= input length)
- Huffman encoding of 'www.example.com' saves space
- encoded_length matches for 'no-cache'
