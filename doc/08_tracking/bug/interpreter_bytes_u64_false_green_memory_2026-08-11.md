# Interpreter byte allocation U64 false-green and memory blow-up

Status: OPEN (P2)
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
