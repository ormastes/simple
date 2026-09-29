# Built-in backend feature acceptance gate

The executable spec is [`builtin_feature_acceptance_gate_spec.spl`](../../../../../test/01_unit/compiler/backend_plugin/builtin_feature_acceptance_gate_spec.spl).

The built-in V1 loader rejects a requested SIMD feature because its compile adapter cannot return backend-confirmed accepted features. A feature-free baseline request remains usable. This is a fail-closed gate for environment-optimized dynamic library REQ-010; it does not establish emitted or executed SIMD evidence.
