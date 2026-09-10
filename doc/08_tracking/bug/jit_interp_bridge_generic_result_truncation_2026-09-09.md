# JIT/interpreter bridge truncates generic `Result` values

Date: 2026-09-09  
Status: root cause corrected locally; focused regression passes and the owner
smoke advances through execution-namespace lookup. `--no-jit` bypasses this defect
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

The failure occurs inside `physical_page_execution_namespace`, when its
unresolvable `spl_wffi_call_i64` bridge returns a full-width signed execution
namespace. `RuntimeValue::from_int` correctly stores values outside the inline
61-bit range as `HeapInt`, but `rt_value_raw_i64` decoded only `HeapUInt` before
rejecting other heap values. The generic `Result` carrier was not the value
being truncated; the original diagnosis confused the enclosing Simple return
type with the nested raw SFFI result.

This is the generic-result counterpart of
`jit_rt_tls13_sha256_returns_empty_2026-08-05.md`; it is not a Slang provider
failure. The native external-provider parity smoke remains green.

## Required fix and acceptance

- Preserve full-width signed i64 results returned by an interpreter-routed
  SFFI call.
- Add a focused runtime regression across both sides of the inline-int bound.
- Rebuild an admitted self-hosted runtime and rerun the Slang owner smoke.
- Reject any fix that merely allowlists the Slang function name.

## Qualification progression

The corrected diagnostic driver reaches `execution_namespace_ready`, proving
that the full-width result now crosses the bridge intact. It then reaches
`cold_generate` and terminates with a separate bus error. The session's
three-cycle cap prevents another owner-smoke retry here; cold-generation
diagnosis and full benchmark qualification remain separate follow-up work.
