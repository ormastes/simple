# SimpleOS native target flow

Mirror of `test/01_unit/compiler/backend/simpleos_native_target_flow_spec.spl`.

The executable SSpec checks that explicit SimpleOS targets survive code generation and sysroot linking, canonical architecture selectors route before hosted linking, RV64 retains its hard-float profile, explicit hosted targets are not inferred as SimpleOS, legacy bare-metal x86 remains supported, aliases normalize correctly, and target resolution precedes host probing.

These are static routing assertions, not boot evidence.
