# Native provider `.so` routed to the SimpleOS registry

## Status

Fixed in source; native end-to-end reverification is pending the next bounded
verification session.

## Reproduction

The Pure Simple provider dispatch runner admitted a real shared object but
failed with `provider-admission-failed:query-symbol-missing`.

`src/os/posix/dynlib.spl` routed ELF shared objects through the SimpleOS kernel
dynamic-library registry. That registry cannot perform hosted `dlopen`/`dlsym`,
so a valid host `.so` could never expose `simple_provider_query_v1`.

## Fix

- Add bounded raw-text host runtime entry points for open, symbol lookup, and
  close.
- Route ELF `.so` artifacts through those hosted entry points.
- Keep SMF artifacts on the SimpleOS registry path.
- Keep provider query wire encoding and provider implementation in Pure Simple.

The runtime boundary performs only the platform loader operation. Composition,
admission, query descriptors, dispatch, and response encoding remain Pure
Simple.

## Evidence and remaining gate

Rust compiler/runtime source checks, C syntax checking, the environment-runtime
audit, and diff checks pass. The already-started end-to-end criterion exhausted
the mandatory three-cycle cap while revealing a second provider dependency on
`str.to_bytes`; the provider now uses the canonical Pure Simple byte-native CLI
result encoder. Its size predicate is tested without allocating a megabyte-size
fixture, avoiding an interpreter-performance regression in the regression test.
Do not claim invocation PASS until a fresh bounded session rebuilds the provider
and runner once with the admitted Pure Simple Stage 2/3 tool.
