# Dynamic Torch facade bypasses lexical raw-SFFI ownership

- Status: OPEN
- Filed: 2026-08-27
- Severity: SFFI authority and provider-admission gap
- Scope: `src/lib/common/torch/dyn_sffi_ops.spl`

## Evidence

The canonical raw declarations in `src/lib/nogc_sync_mut/torch/sffi.spl` are
individually `@unsafe(... capabilities: [ffi])`. The shared dynamic facade
imports those declarations and calls them directly from approximately 129
safe-looking wrapper paths. The facade checks availability, arguments, and
nonpositive handles, but does not place raw calls in lexical
`unsafe(capabilities: [ffi])` owners.

The optional/dynamically loaded libtorch provider has no artifact manifest,
trusted key, ABI registry hash, provider identity, or verification receipt.
It cannot be marked signed or verified.

## Required resolution

1. Keep raw declarations owned only by `nogc_sync_mut/torch/sffi.spl`.
2. Generate or introduce private always-inline lexical raw owners in the
   common dynamic facade, one per distinct ABI contract family.
3. Preserve `Result` wrappers and reject nonpositive handles before they become
   tensor values; retain checked/status-out scalar operations where available.
4. Preserve the hot path: one cached availability decision plus one typed
   provider call; no per-call lookup, hash, signature check, allocation, or
   duplicated tensor operation.
5. Require sealed-complete ABI/evidence admission before any future `signed`
   or `verified` label. Open dynamic libtorch remains unsafe-only.

## Acceptance evidence

- Static audit proves every dynamic-facade raw call is inside a lexical owner.
- Unavailable provider, invalid/null handle, provider failure, and valid handle
  have explicit lane-consistent `Result` outcomes.
- Interpreter/JIT/native registrations share the same contract family.
- A representative tensor-op benchmark shows no new call, copy, allocation,
  lookup, or dispatch overhead.
