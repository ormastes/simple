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
