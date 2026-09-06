# linker_gen section boundary symbols emit three leading underscores, not two

**Filed:** 2026-09-06
**File:** `src/app/linker_gen/main.spl` (`generate_section`, symbol lines)
**Reproduced by:** `test/03_system/feature/app/linker_gen_spec.spl` — "generates
__text_start symbol" / "__text_end" / "__bss_start" / "__bss_end"
(`# @req REQ-LNK-029..032`)

## Symptom

For a section named `.text`, `generate_section` computes:

```simple
val symbol_name = section.name.replace(".", "_")   # ".text" -> "_text"
lines.push("        __{symbol_name}_start = .;")   # "__" + "_text" + "_start"
```

which concatenates to `___text_start` — **three** leading underscores — not
the conventional two-underscore GNU LD boundary-symbol name `__text_start`
that this spec (and, by inspection, the prior hand-authored version of it)
assumed. Confirmed by rendering a real `BoardConfig` with a `.text` section
through `generate_linker_script()` and inspecting the output directly; this
is measured, not inferred from reading the source alone.

The same off-by-one applies to every section name that already carries a
leading dot (`.rodata`, `.data`, `.bss`, `.multiboot`, ...), since
`section.name.replace(".", "_")` only removes the dot, it doesn't remove the
extra underscore the `"__{symbol_name}_..."` template then adds on top.

## Root cause

`"__{symbol_name}_start"` was written assuming `symbol_name` has no leading
underscore (e.g. as if the section name were `"text"`, not `".text"`). But
`section.name` for a real board is dot-prefixed (the same string is rendered
verbatim as `.text :` in the SECTIONS block earlier in the same function),
so `.replace(".", "_")` turns the leading dot into a leading underscore,
which then collides with the template's own leading `__`.

## Impact

Cosmetic but real: every generated linker script's boundary symbols are
`___text_start`/`___text_end`/`___bss_start`/`___bss_end` (etc.) instead of
the conventional `__text_start` etc. Any other tool or documentation that
expects the two-underscore convention (e.g. a C runtime's `extern` boundary
symbol declarations) would fail to link against these.

## Unblock condition

Either strip a leading dot before applying the `_start`/`_end` template
(e.g. `section.name.strip_prefix(".").replace(".", "_")`), or change the
template to `"_{symbol_name}_start"` (single underscore) so the net result is
two total. Once fixed, update the four Symbol Generation scenarios in
`test/03_system/feature/app/linker_gen_spec.spl` back to asserting
`__text_start`/`__text_end`/`__bss_start`/`__bss_end` and remove the `# NOTE:`
comments citing this file.
