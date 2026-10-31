# Seed: `dict[k] ?? default` on an integer-valued Dict returns the raw nil tag

- **Status:** OPEN for the Rust seed. Worked around in `monomorphize_integration.spl` (array constraint maps).
- **Found by:** the Phase 3 bootstrap on macOS aarch64, 2026-10-31. Stage 3, which is the stage2 binary compiling `bootstrap_main.spl`, hit `SIGSEGV` (`EXC_BAD_ACCESS`, address 0) in `MonomorphizationPass.constrain_array_element_v1+280`. That was right after HIR completed, on the main thread, with no deep recursion: frame 25 is `run_monomorphization_with_report`.

## Mechanism

Code native-built by the seed (`SIMPLE_NATIVE_BUILD_RUST=1`) gets these results for a missing key:

| expression | value type | result | expected |
|---|---|---|---|
| `d[k] ?? -1` | `Dict<i64, i64>` | `3` | `-1` |
| `d.get(k) ?? -1` | `Dict<i64, i64>` | `-1` | `-1` |
| `d[k] ?? "dflt"` | `Dict<i64, text>` | `dflt` | `dflt` |
| `d[k] ?? -7` | `Dict<text, i64>` | `nil` | `-7` |

The probe is `test/fixtures/compiler/dict_int_missing_key_coalesce_native.spl`.

The integer-valued index is typed as non-optional, so `??` never sees nil. The tagged nil value (`3`) then flows on as an integer.

In `array_constraint_root_v1`, `self.array_element_roots_v1[symbol.id] ?? -1` therefore returned `3` for an untracked symbol. `constrain_array_element_v1(3, ..)` then read the absent `array_element_types_v1[3]` as a null `HirType` and dereferenced `.kind`.

## Workaround in this change

- Use `.get(k) ?? -1` for the i64-valued root map.
- Guard every `array_element_types_v1[root]` read with `.has(root)`.

## Follow-up

Fix the seed's typing of Dict index expressions with integer value types, so that `??` sees an Optional. Then audit `\] ?? ` uses over integer-valued dicts in `src/compiler/95.interp/execir.spl` (26 sites), `module_loader_lazy.spl`, `package_index_route.spl` and `mir_interpreter.spl`.
