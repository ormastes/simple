# io_runtime process-owner aliases de-JIT the module

## Status

Open compiler/runtime performance blocker discovered during SFFI ownership
consolidation on 2026-08-22.

## Reproduction

Import the canonical process functions into
`src/lib/nogc_sync_mut/io_runtime.spl` with local aliases such as
`process_run as _io_runtime_process_run_owner`, route the existing facade calls
through those aliases, then run:

```text
bin/simple check src/lib/nogc_sync_mut/io_runtime.spl
```

## Observed

The JIT reports `_io_runtime_process_run_owner` as an unresolved external and
drops the whole module to the interpreter, explicitly warning of an expected
100–1000x slowdown. The source checks only because the runtime falls back.

## Expected

An imported function alias must lower to the resolved owner function in JIT and
native lanes, or fail compilation. It must not become an unresolved external or
silently deoptimize the importing module.

## Current containment

`io_runtime.spl` retains five direct process declarations so its hot and widely
used path remains JIT-capable. Each declaration is explicitly unsafe-tagged and
contracted, and each raw call is confined to one allocation-free lexical FFI
scope. Remove those duplicates only after this bug has a regression test and
the canonical-owner form remains JIT-compiled.
