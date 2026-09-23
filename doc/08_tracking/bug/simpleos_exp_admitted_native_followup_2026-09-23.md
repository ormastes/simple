# SimpleOS `exp` admitted-native follow-up

The host Core-C parity selfcheck pins `rt_math_exp(1.0)` to the correctly
rounded binary64 value and exercises the same SimpleOS libc provider source.

TODO after an admitted SimpleOS Phase 2 compiler/image is available: run
`rt_core_c_utf8_math_array_twin_parity_selfcheck` inside QEMU and attach its
non-vacuous check count plus the image/compiler identity. Host-only evidence
must not be promoted as QEMU admission evidence.
