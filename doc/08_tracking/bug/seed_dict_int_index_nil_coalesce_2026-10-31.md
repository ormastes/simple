# Seed: `dict[k] ?? default` on an integer-valued Dict returns the raw nil tag

- **Status:** FIXED in the Rust seed 2026-11-06 (branch `work/seed-jit-miscompiles-20261106`). The `monomorphize_integration.spl` workaround and the `\] ?? ` audit below are no longer required for seed correctness but were not reverted here.

## Fix (2026-11-06)

Root cause: `lower_coalesce` (`src/compiler_rust/compiler/src/hir/lower/expr/control.rs:2189`)
treats an operand typed as a bare scalar (`I64`, `BOOL`, `F64`, ...) as statically
non-nullable and lowers `a ?? d` to `a`. `d[k]` on a `Dict<K, V>` is typed `V`, and MIR
(`lower_index_expr`) unboxes `rt_index_get`'s result, so a miss turned the nil sentinel
into the integer `3` (or printed `nil` for a text key). `d.get(k)` escaped because
`get` is on the optional-accessor list.

Fix: `optionalize_array_accessor` (`hir/lower/expr/helpers.rs`, reached through
`lower_optional_subject` for `??`, `if val`, `match Some/None`) now retypes a
Dict index with a scalar value type to `V?` (`HirType::Pointer`). MIR then keeps the
tagged word, `??` tests presence with `rt_is_some`, and the payload is decoded by
`rt_unwrap_or_self` — the same lane the `[T].first/get` accessors use.

Evidence:
- Rust test `compiler/tests/dict_index_coalesce_jit.rs`: before the fix 3 of 4 FAIL
  (`int_key_int_value_miss_coalesces_to_default`, `text_key_int_value_miss_coalesces_and_counts`,
  `bool_and_float_values_miss_coalesce`); after, 4/4 pass. `list_optional_accessors_jit`
  (8) and `coalesce_single_evaluation` (3) still pass.
- `test/fixtures/compiler/dict_int_missing_key_coalesce_native.spl`, `SIMPLE_EXECUTION_MODE=jit`:
  old seed (`target/bootstrap/simple.exe`, 2026-10-05) `i64idx=3 i64get=-1 textidx=dflt textkey=nil`;
  fixed seed `i64idx=-1 i64get=-1 textidx=dflt textkey=-7` (= interpreter).
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
