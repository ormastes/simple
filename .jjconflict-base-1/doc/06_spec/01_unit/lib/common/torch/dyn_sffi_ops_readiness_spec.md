# Spec: Dynamic Torch SFFI Readiness Surface

Source: `test/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl`

## Behavior

- The shared dynamic Torch SFFI availability helper delegates to
  `rt_torch_available()`.
- The helper is no longer hardcoded to return `false`.
- The check extracts the `dyn_torch_available()` body before asserting, so it
  cannot pass only because another helper mentions the runtime facade.
- The check remains source-level so it can run on hosts without libtorch
  installed.
- The dynamic linalg solve helper delegates to the documented
  `rt_torch_torchtensor_linalg_solve(a, b)` runtime SFFI after checking
  availability instead of returning an unconditional failure handle.
- The Rust runtime exposes the same torchtensor SFFI symbol as an alias for its
  existing linalg solve implementation.
- A runtime smoke calls the public dynamic linalg-solve helper with invalid
  handles and verifies it returns the safe failure handle instead of crashing.

## Covered Requirement

- Torch readiness placeholder blocker: the dynamic SFFI availability surface
  must reflect owner-runtime readiness instead of masking runtime availability.
- Torch linalg placeholder blocker: dynamic `linalg_solve` must call the
  existing owner runtime SFFI when runtime Torch is available.

## Not Covered

- Real libtorch installation or ABI loading.
- Successful linalg solve with real tensor handles.
- Torch manual seed support.
- svLLM tensor-pack manifest parsing or model-pack loading.
