# Hosted C target guard

Mirror of `test/01_unit/compiler/backend/hosted_c_target_guard_spec.spl`.

The executable SSpec verifies allowed host and same-architecture aliases, supported desktop target descriptors, Linux cross-compiler selection, and fail-closed rejection of unsupported architecture, OS, ABI, and width combinations. It also checks that guarding precedes host-runtime compilation and that bare-metal mode remains explicit.

This is policy/source-level evidence; it does not invoke every listed platform toolchain.
