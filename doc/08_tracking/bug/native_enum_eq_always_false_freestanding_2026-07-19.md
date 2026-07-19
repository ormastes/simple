# Native codegen: enum equality reads false for ALL variants on freestanding lane

- **ID:** native_enum_eq_always_false_freestanding_2026-07-19
- **Status:** SOURCE FIXED (staged freestanding execution pending; workaround remains)
- **Severity:** high (silent no-op of entire subsystems; no diagnostic)
- **Lane:** native-build (cranelift, x86_64-unknown-none, --entry-closure --mode dynload)

## Symptom
In the SimpleOS desktop kernel, `config.execution_policy ==
FontExecutionPolicy.Suggested` (font_types.spl,
`font_render_config_valid()`) evaluates **false for every one of the three
variants simultaneously**, tested against a freshly constructed `Suggested`
value in the same probe:

```
[vec-text-probe] policy_suggested=0 policy_preferred=0 policy_required=0
```

Consequence: `font_execution_plan()` returned `[]`, `draw_text_configured()`
returned false before building any glyph batch — the entire vector text
pipeline silently no-oped (zero exceptions, zero pixels). This was the
primary reason SimpleOS desktop text was blank even after the rasterizer
fault fix.

## Workaround (in WC, lands with the glyph chain)
`engine2d_default_font_config_for(...)` pins `execution_target: "cpu"` when
`baremetal_backend != nil`, taking the `target != "auto"` branch in
`font_render_config_valid()` so the broken enum comparison is never
evaluated. Hosted/GPU builds untouched. Post-fix probes:
`plan_len=6 selection_supported=1 exec_target=cpu`.

## Root cause and fix
Custom enum construction returns a fresh tagged runtime handle, but generic MIR
`==`/`!=` lowered to backend integer/pointer comparison. Pure-Simple
`rt_native_eq` also treated every heap handle as text and rejected kind-4 enum
objects. Equality therefore observed allocation identity instead of enum value.

Enum constructors, typed parameters, fields, calls, lets, assignments, and
merges now retain their existing HIR type provenance. Binary equality routes
through `rt_native_eq` only when both operands prove the same custom enum type;
this gate is required because custom enums currently share runtime enum id 0.
The pure runtime compares discriminants and recursively compares payloads with
a bounded nesting depth. Pointer-only registries validate enum, string, and
array handles before dereference; array payloads compare structurally. C/Rust
semantics continue to ignore enum id.

## Regression
The shared cross-target fixture checks a config field against all three fresh
policy variants, plus equal dynamically allocated text payloads and an unequal
payload through a declared field. It also covers raw integer payloads whose low
bits mimic heap handles, equal/unequal generic-versus-packed numeric array
payloads, typed parameters, direct call results, and enum-valued `if`/`match`
merges. These cases prevent hosted C
enum interning from masking missing MIR routing or unsafe payload dereferences.
Existing strict gates cover LLVM/Cranelift on hosted
Linux/macOS/Windows/FreeBSD and AArch64/RV64 QEMU; ARM32/RV32 keep default-LLVM
compile receipts. The original x86_64-unknown-none SimpleOS QEMU proof remains
pending before the workaround is removed.
