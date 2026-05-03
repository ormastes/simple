# Default Native Runtime Shift To C-Core ABI Design

## Scope

Phase 1 is a selection-policy change, not a new runtime implementation. The narrow `core-c` lane is represented by the existing `libsimple_runtime.a` artifact, while the current broad Rust-hosted lane remains `libsimple_native_all.a`.

## Implementation

- `find_runtime_library()` now resolves only the `libsimple_runtime.a` / `simple_runtime.lib` artifact and never falls through to `libsimple_native_all.a`.
- Native-build runtime-bundle parsing accepts:
  `auto`, `core-c`, `core`, `core_c`, `runtime`, `hosted`, `rust-hosted`, `all`.
- `NativeProjectBuilder` resolves the lane from explicit flags first, then `SIMPLE_NATIVE_RUNTIME_BUNDLE`, then compiler-like entry heuristics.
- The closure guard rejects `libsimple_native_all.a` when the selected lane is `core-c`.
- Link failures from the `core-c` lane append a hosted-lane hint so hosted-only extern usage fails clearly.

## Verification

- Rust unit tests cover:
  - auto lane selection for compiler vs non-compiler entries
  - `core-c` and `hosted` aliases
  - the default-lane closure guard
- CLI specs cover:
  - invalid `--runtime-bundle` values failing before build work
  - accepted `core-c` / `hosted` aliases reaching normal build validation
