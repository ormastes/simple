# Crypto Dual Backend Modes

This guide defines the shared runtime/pure-Simple wrapper policy for algorithms
that can run through both implementations. It is intended to be reused for
crypto, compression, key derivation, and similar runtime-vs-pure library pairs.

Implementation entrypoint:
- `src/os/crypto/dual_backend.spl`

## Modes

### `alpha`

Current default mode.

- Runs both runtime-backed and pure-Simple implementations
- Compares outputs
- Stops immediately if outputs differ

Use this while maturing a pure-Simple implementation and proving parity against
the existing runtime-backed path.

### `beta`

Dual-run diagnostic mode.

- Runs both runtime-backed and pure-Simple implementations
- Compares outputs
- Logs a critical diff report with enough information to reproduce the mismatch
- Returns the preferred backend result

Use this when parity work is active and reproduction detail matters more than
failing closed.

### `normal`

Single-implementation production mode.

- Runs only one implementation on the fast path
- Backend preference selects which implementation runs
- Falls back to the other implementation only when the preferred output is empty

Use this after parity is mature enough that dual-run comparison is no longer
needed on the hot path.

## Backend Preference

`DualBackendPreference` chooses which side is preferred:

- `RuntimeFirst`
- `PureSimpleFirst`

`normal` mode uses this directly to decide which implementation runs.

`alpha` and `beta` still execute both implementations, but return the preferred
result when outputs match. In `beta`, the preferred side also wins after a
logged mismatch.

## Dependency Injection

Wrappers should accept an explicit `DualBackendConfig` parameter for dependency
injection, and may also expose a default-config path for convenience.

Recommended pattern:

1. `foo_with_config(..., config: DualBackendConfig)`
2. `foo(...)` delegates to `dual_backend_default_config()`

When the wrapper needs to guarantee that `normal` really runs only one side,
use the `dual_backend_run_*` helpers and pass runtime/pure lambdas. Do not
precompute both outputs and then call a chooser, because that defeats the hot
path policy.

Current reusable surfaces:
- `dual_backend_run_bytes`
- `dual_backend_run_bool`
- `dual_backend_run_u64`
- `dual_backend_run_text`
- matching `dual_backend_choose_*` helpers when the caller already has both
  results available

Useful config helpers:
- `dual_backend_alpha_default_mode()`
- `dual_backend_beta_default_mode()`
- `dual_backend_normal_pure_simple_mode()`
- `dual_backend_alpha_mode(preference)`
- `dual_backend_beta_mode(preference)`
- `dual_backend_normal_mode(preference)`

Legacy compatibility helpers still exist:
- `dual_backend_assert_mode()` -> `dual_backend_alpha_default_mode()`
- `dual_backend_critical_mode()` -> `dual_backend_beta_default_mode()`
- `dual_backend_pure_simple_mode()` -> `dual_backend_normal_pure_simple_mode()`

## First Integration

Reference integration:
- `src/os/crypto/rsa.spl`

This is the pattern to extend to compression, key exchange helpers, signature
families, and other runtime/pure pairs.
