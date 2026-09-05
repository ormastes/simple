# Interpreter JIT file-state hot path

## Status

Open. Source inspection only; no benchmark was run in the no-verification sync
lane.

## Evidence

`jit_record_call` can load the process JIT state, call `jit_mark_symbol_used`
which loads and writes it, then load and write it again for the call counter.
Other query helpers also reload the same file. Therefore recorded calls perform
multiple filesystem operations rather than an O(1) in-memory update.

## Required fix

Design a process-owned in-memory state with explicit synchronization and a
bounded persistence policy. Preserve cross-process semantics or replace them
with an atomic owner protocol. Measure call latency, write frequency, and peak
RSS before and after. Do not silently cache mutable shared state or remove crash
recovery solely to improve a microbenchmark.

## Current containment

Raw file and PID declarations are removed. Canonical owners preserve existing
operation counts, typed read failure, exact one-call writes, and validated PID
identity. No extra I/O was added by the SFFI authority migration.
