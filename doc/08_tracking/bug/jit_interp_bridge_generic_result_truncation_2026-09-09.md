# JIT/interpreter bridge truncates generic `Result` values

Date: 2026-09-09  
Status: open; blocks hybrid-JIT qualification. `--no-jit` bypasses this defect
and exposes the independent global aggregate persistence failure recorded in
`interpreter_global_page_manager_state_lost_2026-09-09.md`.

## Reproducer

Run `test/fixtures/slang_paged_kv_provider/owner_smoke.spl` through the current
bootstrap binary. Model loading and scalar capability probes succeed. The first
cross-module call returning `Result<i64, BackendError>`,
`physical_page_execution_namespace(backend)`, aborts in `rt_value_raw_i64`:

```text
rt_value_raw_i64: refusing to truncate a non-float heap-boxed InterpCall result
```

An explicit `match` does not change the failure. `--mode=interpreter` also does
not prevent the hybrid bridge used by this `run` path.

## Cause

`src/compiler_rust/compiler/src/compilability.rs` function
`return_type_keeps_boxed` preserves tuples, arrays, text, optionals, and
capabilities. It has no arm for generic `Result<T,E>`. The interpreter marshals
the result as a heap-boxed tagged value, while generated caller code attempts
to coerce it to raw `i64`.

This is the generic-result counterpart of
`jit_rt_tls13_sha256_returns_empty_2026-08-05.md`; it is not a Slang provider
failure. The native external-provider parity smoke remains green.

## Required fix and acceptance

- Preserve interpreter-call results whose return type is generic `Result`.
- Add a focused compiler regression test covering both `Ok(i64)` and an enum
  `Err` across the JIT/interpreter boundary.
- Rebuild an admitted self-hosted runtime and rerun the Slang owner smoke.
- Reject any fix that merely allowlists the Slang function name.
