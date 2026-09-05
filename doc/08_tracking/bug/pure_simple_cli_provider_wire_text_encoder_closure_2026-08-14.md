# Pure Simple CLI provider pulled unused text encoder into its archive

## Status

Fixed and verified with the admitted Pure Simple Stage 2 compiler.

## Reproduction

The native CLI provider called the byte-native result encoder, but that encoder
lived in `cli_command_wire.spl` beside command-authoring functions that call
`text.to_bytes()`. Simple packages at module granularity, so the provider
archive still contained an unresolved `str.to_bytes` reference even though the
provider never called the text encoder.

Evidence before the fix:

```text
Build complete: 4 compiled, 0 cached, 0 failed
Archive: provider_cli_native_bytes.a (39 KB)
U str.to_bytes
```

## Fix

Extract `cli_provider_wire.spl` as the provider-safe owner of:

- canonical request decoding;
- byte-native result encoding;
- fixed-width little-endian fields; and
- constant-time response-length validation.

The authoring module re-exports that API for compatibility but owns the
text-to-bytes encoders separately. The provider imports the safe module
directly. No C implementation or private language layout was introduced.

## Verification

Admitted compiler:

- path: `/mnt/data/bs2/final-e73-run2/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
- SHA-256: `2ec71042dd69cf0001fc3f61640c28038a450048f34e416103988b1627431950`

Result:

```text
Build complete: 2 compiled, 2 cached, 0 failed
Archive: provider_cli_native_bytes_v2.a (34 KB)
simple_cli_command_invoke_v1 present
simple_provider_query_v1 present
forbidden str.to_bytes / rt_string_to_bytes imports: none
```

No bootstrap or Rust-seed fallback was used.
