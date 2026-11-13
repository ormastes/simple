# Emitted enum ids depend on enum registration order

- **Date:** 2026-11-13
- **Status:** OPEN
- **Severity:** reproducibility defect. Native object bytes depend on process history. Any lookup whose bare name has more than one candidate may also miscompile silently.
- **Component:** `src/compiler/50.mir/_MirLowering/module_lowering.spl` (`register_enum_runtime_name`), `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (`enum_runtime_id` near :630, the construction path near :6093)

## Not covered by the 2026-08-08 record

`rt_enum_discriminant_is_enum_id_blind_name_hash_2026-08-08.md` is about the
*discriminant* being a hash of the variant name only. This record is about the
*enum id* immediate that native codegen passes to `rt_enum_new`.

## Observation

Two staged native builds of `src/app/lint/main.spl` (329 modules) ran on the run-21 Stage 2.
The only difference was a stubbed, unread function (see the staged-codegen memory fix,
`driver_native_prelower_mir_fingerprint_v1`). They produced 318/320 byte-identical
objects. In the other two (`lib.common.sdn.value`, `compiler.common.assurance.policy_schema`), size
and symbol lists are identical. Only the 32-bit enum-id immediates loaded before
`rt_enum_new` differ, for example in `SdnValue.null`:

```
before: mov w12,#0x8531 ; movk w12,#0xe07c,lsl 16
after:  mov w12,#0x1d31 ; movk w12,#0x6189,lsl 16
```

## Suspected mechanism (from review, not yet proven)

`register_enum_runtime_name` derives the id as a pure FNV hash of `runtime_name`.
`enum_runtime_id` first reads the qualified table. On a miss it falls back to the
bare-name table `enum_runtime_id_index[enum_name]`, where the last registration
wins. So which runtime name, and therefore which id, a construction resolves to depends on
registration order. Anything that perturbs that order or process state can change emitted
bytes without any source change. Open question: neither immediate above equals the FNV
id of any obvious spelling of `SdnValue`/`AssuranceConvention`. Identify their source
first.

## Related variance

The unmodified binary also changes `__simple_str_const_N` numbering in 43/84
objects when only one diagnostic env var (`SIMPLE_MIR_SECTION_PROFILE_FILE`) is added.
Two runs with identical env were 84/84 byte-identical.

## Next step

Emit the id from the resolved qualified runtime name only, failing closed on a bare-name
miss. Then pin it with two builds that differ only in an unrelated env var and assert
byte-identical objects.
