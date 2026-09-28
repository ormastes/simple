# Native optional u64 unwrap loses the numeric value

Status: open runtime/compiler bug; the package archive decoder uses a checked
plain struct until the native optional representation is repaired.

An isolated one-unit no-stub native executable built with the immutable
Stage2 pure-Simple compiler capsule
`build/bootstrap-target56/phase2-runtime-capsules/d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8e5b0bbf3d91fd72741698e8fe0f26ad033c/simple`
tested `"92".to_u64()`, `Some(92u64)`, and `Some(0u64)`. The direct
`"92".to_u64()` value compared as non-nil, but `.unwrap()` printed
`<value:0x5c>`. `Some(92u64).unwrap()` and `Some(0u64).unwrap()` printed
pointer-like integers that were not 92 or 0. A plain struct and tuple each
carried `92` correctly; byte-to-integer conversion returned the expected 9
for the first character of `"92"`.

The probe lived under ignored `build/mini_builds/target6_numeric_option_probe.spl`
and built in about 1.3 seconds. The archive receipt probe caught the product
effect: native decoding accepted `bad` as an offset before the checked struct
repair. The runtime/compiler owner should add a permanent native ABI regression
for optional `u64` return and unwrap, then fix the representation rather than
relying on numeric text intrinsics or optional unwrapping in persisted-input
parsers. The archive workaround does not qualify other optional `u64` call
sites.
