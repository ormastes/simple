# SCI/provider-query ABI digest width mismatch blocks exact admission

Date: 2026-08-16
Status: Open

## Impact

SCI interface groups lock `abi_digest` as one canonical lowercase 64-hex
SHA-256 string, while `SimpleProviderQueryResultV1.abi_digest` is one `u64`.
`app.simple_core.provider_dispatch` can validate that the SCI value is shaped
correctly, but it cannot compare the two identities without an invented,
collision-prone truncation rule. Dynamic activation therefore lacks exact ABI
identity binding even though artifact bytes, query stability, descriptor size,
and major/minor compatibility are checked.

Affected source:

- `src/lib/nogc_sync_mut/composition/types.spl` (`SimpleInterfaceGroupRecordV1`)
- `src/lib/nogc_sync_mut/composition/provider_contract.spl`
  (`SimpleProviderQueryResultV1`)
- `src/app/simple_core/provider_dispatch.spl`

## Required decision

Freeze one lossless wire representation shared by SCI and provider query. The
preferred v2-compatible direction is four ordered `u64` SHA-256 words (or one
fixed 32-byte arena field) with explicit byte order. Do not truncate or hash a
hash into `u64`, and do not compare display text across the ABI.

## Unblock condition

1. Version the query-result prefix without changing existing v1 offsets.
2. Encode/decode the complete digest deterministically in provider and host.
3. Compare the locked SCI ABI digest before publishing a live pin.
4. Add malformed, mismatch, compatible-prefix, and exact-match fixtures plus
   one admitted native execution. Until then, exact ABI admission is blocked
   and no native/SMF provider PASS may be claimed.
