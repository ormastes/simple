# Packed-byte interpreter RSS gate

Use `scripts/check/check-interpreter-packed-byte-rss.shs` when admitting the
retained packed-byte interpreter path. It measures three payloads (1, 4, and
32 MiB) in fresh interpreter processes and retains raw RSS samples plus p50,
p95, and max RSS in `build/interpreter-packed-byte-rss/`.

The gate requires the exact runtime receipt:

```text
simple_execution_mode_v1 requested=interpreter actual=interpreter fallback=false
```

No receipt means `UNAVAILABLE` and a non-zero result. Do not treat a native
run, a JIT run, or a JIT-to-interpreter fallback as equivalent evidence. Every
row must also report the requested length and zero-fill checksum exactly.

The RSS admission is absolute total process RSS, without subtracting a
baseline: `max_rss_kib * 1024 <= payload_bytes * 4`. The retained manifest
contains `raw_relpath`, `raw_sha256`, `p50_rss_kib`, `p95_rss_kib`, and
`max_rss_kib` for audit.

The focused source contract is
`test/03_system/check/interpreter_packed_byte_rss_gate_contract_spec.spl`.
