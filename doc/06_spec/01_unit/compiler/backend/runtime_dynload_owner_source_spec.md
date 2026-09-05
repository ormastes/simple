# Hosted dynamic-loader ownership

Mirror of `test/01_unit/compiler/backend/runtime_dynload_owner_source_spec.spl`.

The executable source-contract spec verifies there is one tagged C dynamic-loader owner when native-all is absent and that the runtime-native fallback remains guarded and encoding-identical.

It validates ownership in source; it does not load a shared library at runtime.
