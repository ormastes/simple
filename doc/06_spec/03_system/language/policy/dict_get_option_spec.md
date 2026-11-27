# Dict.get returns Option (Some/None)

**Requirement:** Dict.get returns Option
**Specs:** `test/03_system/language/policy/dict_get_option_spec.spl` (implemented), `test/03_system/language/policy/dict_get_option_indev_spec.spl` (@tag:in-development)
**Probe:** `test/03_system/language/policy/probe/dict_get_option_probe.spl` run under the interpreter and the JIT engine.

| Scenario | Spec | Status |
|---|---|---|
| interpreter lane reaches the probe | main | passing |
| JIT lane reaches the probe | main | passing |
| interpreter: hit_is_some | main | passing |
| interpreter: stored_zero_is_some | main | passing |
| interpreter: miss_is_none | main | passing |
| interpreter: inline_match_none | main | passing |
| interpreter: text_some | main | passing |
| interpreter: text_none | main | passing |
| interpreter: inline_match_some | main | passing |
| jit: hit_is_some | main | passing |
| jit: stored_zero_is_some | main | passing |
| jit: miss_is_none | main | passing |
| jit: inline_match_none | main | passing |
| jit: text_some | main | passing |
| jit: text_none | main | passing |
| jit: inline_match_some | indev | in-development (fails now) |
| interpreter and JIT print identical PROBE lines | indev | in-development (fails now) |
