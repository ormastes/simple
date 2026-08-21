# Caret cannot yet launch Slang local inference

## Status

Open. `config/check/must_check_gates.sdn` keeps
`caret-local-llm-launch` as a non-passing bootstrap TODO.

## Evidence

- `src/lib/gc_async_mut/slang/` supplies tensor-pack loading and streaming
  readiness, but no token-generation request/response endpoint.
- `src/app/llm_caret/provider.spl` dispatches `local_torch`; it has no `slang`
  provider.
- `scripts/check/check-caret-suite-bootstrap.shs --gate local-torch` currently
  checks the independent Python/Torch provider and therefore is not Slang
  launch evidence.

## Unblock condition

The Slang owner must expose a bounded native generation endpoint with model and
request lifecycle receipts. The Caret owner must add an explicit `slang`
provider that calls it. A bootstrap system test must launch the local service,
submit a non-vacuous prompt through Caret, validate output/provider identity,
and stop the service without leaked child processes. Only that checker may
promote `caret-local-llm-launch` to automated/PASS.
