# Interpreter byte allocation U64 false-green and memory blow-up

Status: FIXED 2026-11-25 (interpreter defect verified fixed in the deployed
seed; the admitted self-hosted Stage-4 RSS proof remains open — see the
2026-11-25 verification note at the bottom).
Status re-verified 2026-08-17 by source inspection (triage shard 02).

This is a condensed restoration of the tracking record originally introduced
by commits `08424ed7075` and `eaae2e73dc5`, restated against current source.

## Status
The length/oracle and packed-byte implementation are present in the integrated
lineage; admission and RSS proof remain pending.

## Reproduction
The historical bootstrap-seed run of
`test/05_perf/bytes_push_1mib.spl` reported length `0` for the 1 MiB, 4 MiB,
and 32 MiB cases, exited successfully, took 7.32 s, and peaked at 2,730,740
KiB RSS. Those observations are
diagnostic rather than self-hosted release evidence.

## Root cause and repairs
The fixture formerly declared `rt_bytes_alloc(len: u64)` while the interpreter
extern accepted only signed integers and boxed every byte as a `Value`. The
fixture now fails closed on requested length, endpoints, and zero-fill checksum.
The current interpreter boundary accepts checked integer lengths and returns
first-class packed `ByteArray` storage; `StrBytes` remains text and is not used
as a byte-array substitute.

## Unblock condition
Run the exact 1/4/32 MiB oracle on an admitted self-hosted Stage 4 and prove
packed storage with bounded RSS on an admitted self-hosted binary: correct
length, content, and checksum plus peak RSS no greater than four times payload
without baseline subtraction. The admitted self-hosted memory row remains open.

## Triage 2026-09-13 (BUGFIX-7 lane)

Out of lane: the fix surface is src/compiler_rust/compiler/src/value.rs (Rust interpreter byte-allocation path), needs a seed rebuild to verify any change. No change made.

## 2026-11-06 fix (work/interp-p2-seed)
Root cause of the garbage bytes: `runtime_bridge.rs` `value_to_runtime_inner` marshalled
`Value::ByteArray` across the hybrid-interp-splice as one heap-boxed `UInt` RuntimeValue
per byte; JIT `[u8]` reads took the pointer bits as the byte (`rt_bytes_alloc(8)` gave 49,..,
checksum 126953776 for 1 MiB) and 1 MiB cost ~1M heap allocations. It now crosses as one packed
runtime byte array (`rt_bytes_from_raw`). The bench also treated `env_get` "" as set; fixed.
Test-only seed (not deployed): bench prints len=1048576/4194304/33554432, checksum=0, rc=0.
Rust unit: `runtime_bridge::tests::test_value_to_runtime_byte_array_is_packed_bytes`.
Spec: `test/01_unit/interpreter/bytes_alloc_zero_fill_spec.spl`. Verify on next seed deploy.

## Verification note (2026-11-25, Windows host, deployed seed)

The 2026-11-06 fix (`27ebe8174cc` "fix(seed-interp): packed [u8] bridge, ...")
is present in source at
`src/compiler_rust/compiler/src/runtime_bridge.rs:90-97` —
`Value::ByteArray`/`FrozenByteArray` now cross the hybrid-interp-splice as one
packed runtime byte array via `rt_bytes_from_raw`, not one heap-boxed `UInt`
per byte. The deployed `bin/simple.exe` (committed 2026-11-17, after the fix)
contains it. Live verification on this host with a minimal probe that avoids
the decorator-blocked stdlib (`extern fn rt_bytes_alloc` only):

```
len=8
checksum=0
big_len=1048576
big_checksum=0
```

`rt_bytes_alloc(8)` no longer reads back pointer-bit garbage (was 49,...)
and the 1 MiB case reports correct length and zero-fill checksum (was
len=0 / checksum=126953776). The false-green + garbage-bytes defect named by
this bug is fixed in the deployed seed.

Limit / still open: the full `test/05_perf/bytes_push_1mib.spl` oracle run is
blocked at HEAD by the known release/1.0.0 source/binary inconsistency (the
pinned seed rejects `@representation_boundary` from cfd89933699 while parsing
`std.io_runtime`), and the admitted self-hosted Stage-4 RSS-bound proof (peak
RSS <= 4x payload on an admitted self-hosted binary) still requires a
self-hosted binary that does not exist on this host. That admission row
remains open exactly as the "Unblock condition" section states; this note
closes only the interpreter defect.
