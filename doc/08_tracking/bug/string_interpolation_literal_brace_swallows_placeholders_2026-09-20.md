# String interpolation: a literal `{...}` pair swallows following `{placeholder}` segments in the same literal

- Status: OPEN (2026-09-20) — affects the seed lexer today; check whether the pure-Simple compiler (`src/compiler`) reimplements the same scan before closing.
- Found: 2026-09-20 (kernel_plugin_schema generator lane)
- Component: string-literal interpolation scanner (seed `bin/simple`; likely `src/compiler` frontend too)

## Observation

Scanner behavior, established by probes:

- It scans each string literal for `{`, then pairs it with a balanced/nested close. If the enclosed candidate is a valid expression it interpolates; if the literal ends first, the `{` is emitted raw and scanning resumes after it (so `"x={x} {"` and `"{ x={x}"` work).
- BUT when the candidate is balanced yet not a valid expression — e.g. a literal brace pair containing placeholders, as in `"    { name: \"{vector.name}\", size: {vector.size} },"` — the WHOLE `{...}` span is emitted raw and scanning resumes after the final `}`. Every placeholder inside a balanced literal-brace span is silently left as literal text.

Concrete impact: `src/tool/kernel_plugin_schema/generate_{rust,c,cpp}.spl` vector-emitting lines wrapped their placeholders in literal C/Rust/C++ braces and emitted `{vector.name}` verbatim into generated sources (the KPF specs failed with "to contain invalid_alignment" etc.). Fixed on 2026-09-20 by emitting literal braces through the `{{`/`}}` escapes instead. The `{{`/`}}` escapes work correctly.

## Fix direction

1. On balanced-but-invalid candidates, fall back to emitting only the OPENING `{` raw and rescan the remainder (same rule as the unbalanced case) instead of swallowing the whole span.
2. Add scanner unit tests: `"{{"`, `"{ x={x}"`, `"{{expr}}"`, literal-brace-then-placeholder mixtures.

## Related

- `unit_test_sweep_macos_2026-09-17.md` (tools lane kernel_plugin_schema x4 root causes)
