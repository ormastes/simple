# Default Native Runtime Shift To C-Core ABI Design

## Scope

Phase 1 is a selection-policy change that also makes the lane names explicit. The narrow non-hosted lanes use `libsimple_runtime.a`: `simple-core` when a pure-Simple archive is present, otherwise `core-c-bootstrap`. The broad hosted lane remains `libsimple_native_all.a`.

## Implementation

- `find_runtime_library()` now resolves the bootstrap `core-c-bootstrap` lane archive only; `find_simple_core_runtime_library()` resolves the pure-Simple `simple-core` lane archive separately.
- Native-build runtime-bundle parsing accepts:
  `auto`, `simple-core`, `core-c-bootstrap`, `core-c`, `core`, `core_c`, `runtime`, `hosted`, `rust-hosted`, `all`.
- `NativeProjectBuilder` resolves the lane from explicit flags first, then `SIMPLE_NATIVE_RUNTIME_BUNDLE`, then compiler-like entry heuristics, and `auto` prefers `simple-core` over `core-c-bootstrap` for non-compiler entries.
- The closure guard rejects `libsimple_native_all.a` when the selected lane is `simple-core` or `core-c-bootstrap`.
- Link failures from the selected core lane append a hosted-lane hint so hosted-only extern usage fails clearly.

## Verification

- Rust unit tests cover:
  - auto lane selection for compiler vs non-compiler entries, including `simple-core` preference when present
  - `simple-core`, `core-c-bootstrap`, and hosted aliases
  - the default-lane closure guard
- CLI specs cover:
  - invalid `--runtime-bundle` values failing before build work
  - accepted semantic and legacy lane names reaching normal build validation
