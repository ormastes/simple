# BUG: LLM Caret compiled carrier cannot be produced within bounded build time

- **ID:** `llm_caret_compiled_carrier_build_latency`
- **Severity:** P1 (blocks production compiled database/plugin carriers)
- **Found:** 2026-08-02
- **Status:** OPEN

## Symptom

The focused messaging source checks and interpreter-mode SSpecs converge, but a
native entry-closure build for `messaging/hook_worker.spl` does not complete
within the repository's 120-second bounded verification window. The same class
of timeout affects the larger database and MCP carriers. No executable artifact
is produced under `build/database/`.

Standalone SMF is not currently an alternative: the compiler correctly rejects
the PureDatabase closure because 57 reachable functions still require
interpreter-only `PatternMatch`, `TryOperator`, collection operations, or
collection literals.

## Reproduction

```sh
SIMPLE_TIMEOUT_SECONDS=120 bin/simple native-build \
  --source src/app --source src/lib --entry-closure \
  --entry src/app/llm_caret/messaging/hook_worker.spl \
  --strip --output build/database/llm_caret_messaging_hook
```

The watchdog terminates the build at 120 seconds without an artifact.

## Required resolution

- Profile frontend/module loading and entry-closure construction for this
  realistic PureDatabase application.
- Cache compiler/module analysis across the four messaging carrier builds.
- Meet a cold build target below 120 seconds and provide a materially faster
  warm rebuild.
- Alternatively, lower the remaining PureDatabase closure constructs for
  standalone SMF without interpreter fallback.

Until resolved, production startup must fail closed when the cached compiled
carrier is missing or stale. Interpreter execution is diagnostic-only.

## Additional backend evidence

A bounded build of the smallest hook carrier with `--backend cranelift` and a
dedicated cache also completed without producing an executable artifact. The
failure is therefore not demonstrated to be LLVM-only; frontend closure
construction/lowering remains part of the investigation scope.

The smaller `src/app/postgres_mimic_server/main.spl` native entry closure also
produced no artifact. Its standalone SMF diagnostic reports 36 unsupported
functions, primarily `TryOperator` and `PatternMatch` in PureDatabase plus CLI
helpers. This is the current finite lowering target for a reusable compiled
database process.

The newest available self-hosted `simple-bootstrap` bypasses that Rust-seed
gate and reaches HIR lowering, but its focused compile command bulk-loads
`nogc_async_mut/async/future.spl`. Passing `--entry-closure` does not alter that
behavior, and compilation stops on missing generic monomorphization before an
artifact can be emitted.

Closure transport was audited after the self-hosted failure. Its initial `0`
state is intentional: the driver uses it to walk the entry import graph, then
sets the state to `1` before suppressing whole-project loading. Pre-setting `1`
would skip closure discovery, so no such change is retained. The unexpected
generic async module must instead be removed from the database entrypoint's
reachable dependency graph or supported by native monomorphization.

Removing `std.cli.cli_util` from the PostgreSQL-mimic entry eliminated the
generic-async failure. The third bounded self-hosted attempt reached MIR, where
imported database methods were unresolved, lowered to const-zero placeholders,
and caused a nil-receiver crash (exit 132, Task #145). Owner-module free
façades now replace open/startup/query/close plus map/join rendering. Their
closure contract test exits 0; the three-cycle guard prevented another compile.
