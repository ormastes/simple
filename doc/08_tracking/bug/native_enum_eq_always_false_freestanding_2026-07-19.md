# Native codegen: enum equality reads false for ALL variants on freestanding lane

- **ID:** native_enum_eq_always_false_freestanding_2026-07-19
- **Status:** OPEN (workaround in engine2d: route around the comparison)
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

## Related
Same family as the cross-module VHDL enum defect (2026-07-18 notes) and the
BoxInt tag-shift class: enum tag representation appears inconsistent between
construction site and comparison site on this lane.

## Fix direction
Audit freestanding-lane enum tag compare: the compare likely reads a
tagged/boxed representation on one side and a raw discriminant on the other.
A regression test should construct each variant and `==`-compare against
itself inside a --target x86_64-unknown-none build.
