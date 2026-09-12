# macOS bootstrap Rust-hosted archive lacks `copy_mem`

**Status:** CLOSED-STALE (2026-09-12: no parseable status and no cheap repro in the record; reopen with a fresh repro against the current seed)

## Status

Resolved in source and focused runtime verification on 2026-07-17. The broader
Stage 3/4 bootstrap remains open under its own provider-selection gate.

## Evidence

The corrected `main` sources were compiled with the fresh Stage 3 compiler and
the isolated cache under `build/native_probe/main_closure/cache-stage3`.
`build/native_probe/main_closure/logs/stage3-fixed2.log` ends with:

```text
Undefined symbols for architecture arm64:
  "_copy_mem", referenced from:
      _compiler_rust__lib__std__src__core__list__List_dot_reserve
```

`copy_mem` is implemented by the monolithic `runtime_native.c` and pure-Simple
`simple_core/core_memory.spl`, but the Rust-hosted archive currently exports
only `rt_memcpy` from `runtime_memory.c`. The failure is therefore provider
composition, not source lowering.

## Resolution

`runtime_memory.c` now gives the Rust-hosted memory component an ABI-compatible
`copy_mem` owner that forwards to `rt_memcpy`. The focused runtime suite passes
7/7, including guard-byte and returned-destination assertions, and the rebuilt
`libsimple_native_all.a` exports both `_copy_mem` and `_rt_memcpy`.

The cached Stage 3 link no longer reports `_copy_mem`. Its current failure is a
separate invocation/provider-selection issue: the old Stage 3 driver selected
`target/bootstrap/deps/libsimple_runtime.a` instead of
`libsimple_native_all.a`, leaving 73 hosted compiler hooks unresolved. Resume
with the explicit bootstrap hosted-bundle selector in a fresh bounded turn.

## Triage 2026-09-12

Status line inserted mechanically by the bug-db triage (record had no parseable `Status:` line); rule: filed before 2026-07-29 with no cheap repro → CLOSED-STALE, otherwise OPEN (unverified).
