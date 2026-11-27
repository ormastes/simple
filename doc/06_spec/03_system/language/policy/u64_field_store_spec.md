# Declared u64 fields hold unsigned values

**Requirement:** u64 field store
**Specs:** `test/03_system/language/policy/u64_field_store_spec.spl` (implemented), `test/03_system/language/policy/u64_field_store_indev_spec.spl` (@tag:in-development)
**Probe:** `test/03_system/language/policy/probe/u64_field_probe.spl` run under the interpreter and the JIT engine.

| Scenario | Spec | Status |
|---|---|---|
| interpreter lane reaches the probe | main | passing |
| JIT lane reaches the probe | main | passing |
| interpreter: small_value_unchanged | main | passing |
| jit: small_value_unchanged | main | passing |
| jit: class_store_high_bit_nonneg | main | passing |
| jit: class_store_minus1_nonneg | main | passing |
| jit: struct_store_minus1_nonneg | main | passing |
| jit: ctor_minus1_nonneg | main | passing |
| jit: field_equals_typed_local | main | passing |
| interpreter: class_store_high_bit_nonneg | indev | in-development (fails now) |
| interpreter: class_store_minus1_nonneg | indev | in-development (fails now) |
| interpreter: struct_store_minus1_nonneg | indev | in-development (fails now) |
| interpreter: ctor_minus1_nonneg | indev | in-development (fails now) |
| interpreter: field_equals_typed_local | indev | in-development (fails now) |
| interpreter and JIT print identical PROBE lines | indev | in-development (fails now) |
