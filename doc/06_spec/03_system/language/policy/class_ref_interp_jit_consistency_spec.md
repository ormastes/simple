# Class references are shared (interpreter vs JIT)

**Requirement:** ADR-004
**Specs:** `test/03_system/language/policy/class_ref_interp_jit_consistency_spec.spl` (implemented), `test/03_system/language/policy/class_ref_interp_jit_consistency_indev_spec.spl` (@tag:in-development)
**Probe:** `test/03_system/language/policy/probe/class_ref_probe.spl` run under the interpreter and the JIT engine.

| Scenario | Spec | Status |
|---|---|---|
| interpreter lane reaches the probe | main | passing |
| JIT lane reaches the probe | main | passing |
| interpreter: param | main | passing |
| jit: param | main | passing |
| jit: field_orig_to_holder | main | passing |
| jit: field_holder_to_orig | main | passing |
| jit: list_elem_to_orig | main | passing |
| jit: list_orig_to_elem | main | passing |
| jit: dict_orig_to_value | main | passing |
| jit: field_reassign | main | passing |
| jit: alias | main | passing |
| interpreter: field_orig_to_holder | indev | in-development (fails now) |
| interpreter: field_holder_to_orig | indev | in-development (fails now) |
| interpreter: list_elem_to_orig | indev | in-development (fails now) |
| interpreter: list_orig_to_elem | indev | in-development (fails now) |
| interpreter: dict_orig_to_value | indev | in-development (fails now) |
| interpreter: field_reassign | indev | in-development (fails now) |
| interpreter: alias | indev | in-development (fails now) |
| interpreter and JIT print identical PROBE lines | indev | in-development (fails now) |
