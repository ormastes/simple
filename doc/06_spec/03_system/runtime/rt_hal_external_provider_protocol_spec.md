# External RT/HAL Provider Protocol — Supporting Manual

Executable: `test/03_system/runtime/rt_hal_external_provider_protocol_spec.spl`  
Requirements: REQ-008, REQ-009, REQ-010, REQ-014  
Status: **unverified** — the self-hosted `bin/simple` runtime is absent in this
worktree, so SPipe generation was not executed.

## Purpose and boundary

This supporting scenario checks admission data for the real C and Rust RT/HAL
provider fixtures. It does not claim that either foreign executable was built
or that provider parity ran. The primary parity evidence remains
`rt_hal_provider_differential_spec.spl`.

## Operator flow

1. **admit pinned external provider toolchains** — create the bounded typed
   plan; assert two admitted tools, static/no-PIE C flags, static Rust link
   options, and SHA-256 identity pins.
2. **admit exact external provider executables** — create the sealed V3 comparison plan;
   assert no additional process instruction, a two-provider/4096-byte bound,
   stable C/Rust IDs, and exact identity hashes.

## Evidence and limitations

Execute once with:

```text
bin/simple spipe-docgen test/03_system/runtime/rt_hal_external_provider_protocol_spec.spl --output doc/06_spec --no-index
bin/simple test test/03_system/runtime/rt_hal_external_provider_protocol_spec.spl --mode=interpreter
```

Toolchain absence, hash mismatch, malformed child output, or an unavailable
provider is fail-closed/blocked evidence, not a successful comparison. The
deprecated public V2 setup and direct public V3 setup must reject before a
partial host installation; only the compiler-owned staged V3 route may become
Ready.
