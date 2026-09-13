# `SimpleProviderQueryResultV2` wire codec is missing; `os/smf/provider_query_wire.spl` imports nonexistent digest symbols

- Status: OPEN (2026-09-13)
- Found by: BUGFIX-7 lane while fixing
  `sci_provider_query_abi_digest_width_mismatch_2026-08-16`.
- Component: `src/os/smf/provider_query_wire.spl`,
  `src/lib/nogc_sync_mut/composition/provider_contract.spl`
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed), sha256
  prefix `3d120a6f`, at commit `a6450c9d6f5`.

## Symptom

```
bin/simple test test/01_unit/app/simple_core/provider_abi_digest_admission_spec.spl
✗ keeps every V1 field at its V1 offset and appends 32 digest bytes
✗ decodes a V1-only provider's 60 written bytes as an undeclared digest
semantic: function 'encode_provider_query_result_v2' not found
```

## Root cause

`test/01_unit/app/simple_core/provider_abi_digest_admission_spec.spl` imports
`SimpleProviderQueryResultV2`, `SIMPLE_PROVIDER_QUERY_RESULT_V2_SIZE` from
`std.nogc_sync_mut.composition.provider_contract` and
`encode_provider_query_result_v2`/`decode_provider_query_result_v2` from
`os.smf.provider_query_wire`. None of the four exist anywhere in `src/`
(`grep -rl` returns nothing). This looks like a spec written ahead of a V2
wire-format implementation that was never landed.

Separately and more seriously: `src/os/smf/provider_query_wire.spl` itself
imports `SimpleProviderDigestV1`, `simple_provider_digest_zero_v1`,
`simple_provider_digest_is_zero_v1` from `provider_contract` — **none of
which exist there either**. `provider_contract.spl`'s
`SimpleProviderQueryResultV1.abi_digest` is a plain `u64` today (not the old
8-word `SimpleProviderDigestV1`), so this file's V1 encode/decode path
(`_push_digest_v1`, `_read_digest_v1`, the `PROVIDER_QUERY_RESULT_V1_ABI_DIGEST_OFFSET`/`_RESERVED_OFFSET`
layout assuming a 32-byte digest) is stale relative to the current contract
and does not compile/resolve cleanly. The interpreter's late (call-site,
not import-time) resolution of missing symbols is why this has not surfaced
as a hard failure everywhere that transitively imports it.

`src/os/smf/provider_loader.spl` and `src/app/provider_cli/native_provider_v1.spl`
also import digest helper names
(`simple_provider_digest_is_canonical_v1`, `simple_provider_digest_equal_v1`,
`simple_provider_digest_from_hex_v1`, `simple_provider_digest_zero_v1`) that
do not exist in `provider_contract.spl` either. This reads as an incomplete
migration: `provider_contract.spl` was slimmed from a richer digest API
(8-word `SimpleProviderDigestV1` + several helper fns) down to a bare `u64`
field plus the new `SimpleAbiDigest256V1`/`abi_digest.spl` module, and the
consumers were never updated to match.

## What this lane fixed (separate commit)

Only `app.simple_core.provider_dispatch.simple_core_provider_abi_digest_verdict_v1`
was added — a small, self-contained pure function with no dependency on the
broken wire/loader code, closing the spec's "host-side exact ABI admission
verdict" describe block (5/5 green). The "provider query result V2 wire"
describe block (2 examples) is NOT fixed and needs this record's larger repair.

## Fix direction (not attempted — out of budget for this lane)

1. Update `provider_query_wire.spl`'s V1 codec to match the current
   `abi_digest: u64` field (8-byte scalar at offset 48, reserved at 56,
   total 60 bytes matching `SIMPLE_PROVIDER_QUERY_RESULT_V1_SIZE`), dropping
   the dead `SimpleProviderDigestV1`-shaped helpers.
2. Add `SimpleProviderQueryResultV2` (`base: SimpleProviderQueryResultV1`,
   `abi_digest_256: SimpleAbiDigest256V1`) and
   `SIMPLE_PROVIDER_QUERY_RESULT_V2_SIZE` (`= V1_SIZE + 32`) to
   `provider_contract.spl`.
3. Add `encode_provider_query_result_v2`/`decode_provider_query_result_v2` to
   `provider_query_wire.spl`: V1 bytes verbatim, followed by the 4 big-endian
   `u64` words of `abi_digest_256` (per `abi_digest.spl`'s frozen byte order).
4. Separately audit and repair `provider_loader.spl` and
   `native_provider_v1.spl`'s missing digest-helper imports — a distinct
   defect from the V2 wire gap, found while tracing this one.
