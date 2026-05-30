# Baremetal `[u8]` direct index equality diverges from byte accessor

Date: 2026-05-30
Status: Open
Severity: High

## Symptom

In the x86_64 freestanding TLS unit image, direct `[u8]` indexing in an equality
expression failed for a TLS record header even though `rt_bytes_u8_at(record, 0)`
returned the correct byte value `23` (`0x17`).

Observed during D8:

```simple
enc8[0] == 0x17u8
```

failed while:

```simple
rt_bytes_u8_at(enc8, 0) == 0x17
```

passed.

## Expected

Direct `[u8]` indexing should produce the same byte value as `rt_bytes_u8_at`
in freestanding native code, and equality against `u8` literals should compare
numeric byte values without tag or width divergence.

## Next Probe

Add a minimal freestanding/native regression that creates `[0x17u8, 0x03u8]`
and asserts both:

```simple
xs[0] == 0x17u8
xs[0].to_i64() == 23
```

Then compare the emitted MIR/codegen for index result type and equality
lowering against the runtime byte accessor path.
