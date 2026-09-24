# SCI/provider-query ABI digest width mismatch

Date: 2026-08-16
Status: Fixed in focused slice

## Impact

SCI locks one canonical lowercase 64-hex SHA-256 interface identity, while the
provider query previously returned only one `u64`. Exact admission therefore
had no lossless comparison and any truncation rule would permit collisions.

## Resolution

The query-result wire preserves bytes 0..47, carries the complete digest in
bytes 48..79, reserves zero bytes 80..83, and requires an exact 84-byte record.
Pure-Simple producers and consumers use eight ordered `u32` words so no native
Simple object or text layout crosses the boundary. Loader session query
compares the complete result with the canonical SCI digest before issuing a
pin. The host poison-fills all 84 result bytes before invocation, so a legacy
provider that writes only 60 bytes leaves a nonzero reserved suffix and fails
closed. Focused fixtures cover canonical parsing, exact match, mismatch,
partial legacy writes, reserved bytes, and provider round-trip.

## Re-check 2026-09-13 (BUGFIX-7 lane)

`app.simple_core.provider_dispatch.simple_core_provider_abi_digest_verdict_v1`,
the host-side admission function this record's own contract implies, did not
exist in the tree (`test/01_unit/app/simple_core/provider_abi_digest_admission_spec.spl`
RED: `semantic: function 'simple_core_provider_abi_digest_verdict_v1' not
found`, 7 of 11 examples failing). Implemented it in
`src/app/simple_core/provider_dispatch.spl` per the spec's own contract
(exact-match -> `""`, prefix-collision/unrelated mismatch ->
`"provider-abi-digest-mismatch"`, all-zero provided digest ->
`"provider-abi-digest-not-declared"`, malformed locked hex -> a
`"provider-abi-digest-locked-invalid:..."` diagnostic), using the existing
`simple_abi_digest_parse_hex_v1`/`simple_abi_digest_equals_v1`/`simple_abi_digest_is_zero_v1`
helpers in `abi_digest.spl`.

```
Before: bin/simple test test/01_unit/app/simple_core/provider_abi_digest_admission_spec.spl
        Results: 11 total, 4 passed, 7 failed
After:  Results: 11 total, 9 passed, 2 failed
```

The remaining 2 failures are a separate, larger defect (a missing V2 wire
codec plus stale digest-type imports in `os/smf/provider_query_wire.spl` and
sibling files) — filed as
`doc/08_tracking/bug/provider_query_result_v2_wire_codec_missing_2026-09-13.md`.
Directory sweep before/after (`test/01_unit/app/simple_core/`):
`29 total, 11 passed, 18 failed` -> `29 total, 16 passed, 13 failed` — only
this spec's numbers moved.

Status: PARTIALLY FIXED (2026-09-13) — verdict function implemented and
green; V2 wire codec remains open in the sibling record above.

## Explicit exclusion

Mutable pathname replacement and same-handle loader TOCTOU protection are not
part of this fix. They remain a separate loader criterion and must not be
claimed by this ABI identity result.

## Focused admitted evidence

- Pure-Simple Stage-2 compiler:
  `/mnt/data/bs2/final-e73-run2/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-admitted/simple`
- Compiler SHA-256:
  `2ec71042dd69cf0001fc3f61640c28038a450048f34e416103988b1627431950`
- Supported command used: `native-build`; isolated caches and outputs were
  retained under `/mnt/data/tmp/simple-main-bootstrap-abi-digest-recovery/`.
- `abi_digest_admission_runner` cycle 2 verifies the poison-filled partial
  legacy write and an explicit nonzero reserved byte in addition to the exact
  digest cases: 37 compiled, 0 cached, 0 failed; executable SHA-256
  `78cc77efc6b334962d29b5146cbeba05f74ead29ad9ccd2d6170016b3dc2f224`;
  execution printed `abi-digest-admission=pass` and exited 0.
- `abi_digest_producer_runner` cycle 2: 4 compiled, 0 cached, 0 failed;
  executable SHA-256 `7cb29699d3de2c1ab90b35f722c2df0150fe21ea2aa65cc163cb992484aadfac`;
  execution printed `abi-digest-producers=pass` and exited 0.
- Native provider archive: 4 compiled, 0 cached, 0 failed. Provider dispatch
  archive: 40 compiled, 0 cached, 0 failed. No Rust-seed, Stage-4, full
  bootstrap, dynamic-provider activation, or TOCTOU evidence was used.
- `check-cli-provider-v1-host.shs` passed with the owned 84-byte C producer and
  84-byte host buffer. Its only compiler warning is the pre-existing ignored
  `write` return in unrelated `rt_net_http_plain_local_probe`.
