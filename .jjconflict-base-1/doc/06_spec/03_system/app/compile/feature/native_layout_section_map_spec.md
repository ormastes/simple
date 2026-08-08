# Native Layout Section Map Specification

> 1. "#define SIMPLE LAYOUT SECTION dispatch   attribute

<!-- sdn-diagram:id=native_layout_section_map_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_layout_section_map_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_layout_section_map_spec -> std
native_layout_section_map_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_layout_section_map_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Layout Section Map Specification

## Scenarios

### Native Layout Section Map Contract

### section map parsing

#### should parse generated-C layout section map macros

1. "#define SIMPLE LAYOUT SECTION dispatch   attribute
   - Expected: entry.valid is true
   - Expected: entry.symbol_name equals `dispatch`
   - Expected: entry.macro_name equals `SIMPLE_LAYOUT_SECTION_dispatch`
   - Expected: entry.section_name equals `.text.simple.hot.0.dispatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = native_layout_section_map_entry_from_line(
    "#define SIMPLE_LAYOUT_SECTION_dispatch __attribute__((section(\".text.simple.hot.0.dispatch\"), used))"
)
expect(entry.valid).to_equal(true)
expect(entry.symbol_name).to_equal("dispatch")
expect(entry.macro_name).to_equal("SIMPLE_LAYOUT_SECTION_dispatch")
expect(entry.section_name).to_equal(".text.simple.hot.0.dispatch")
```

</details>

#### should reject malformed or unsafe section map lines

1. "#define SIMPLE LAYOUT SECTION dispatch   attribute
   - Expected: bad_section.valid is false
   - Expected: bad_section.reason equals `invalid_section`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val malformed = native_layout_section_map_entry_from_line("#define SIMPLE_LAYOUT_SECTION_dispatch")
expect(malformed.valid).to_equal(false)
expect(malformed.reason).to_equal("malformed_define")

val bad_section = native_layout_section_map_entry_from_line(
    "#define SIMPLE_LAYOUT_SECTION_dispatch __attribute__((section(\".data.dispatch\"), used))"
)
expect(bad_section.valid).to_equal(false)
expect(bad_section.reason).to_equal("invalid_section")
```

</details>

### generated C application

#### should apply section attributes to matching generated C functions

1. "#define SIMPLE LAYOUT SECTION dispatch   attribute
2. "#define SIMPLE LAYOUT SECTION parse   attribute
3. ] join
4. "static int dispatch
5. "int parse
6. "  return dispatch
7. "int main
8. "  return parse
9. ] join
   - Expected: applied.enabled is true
   - Expected: applied.applied_count equals `2`
   - Expected: applied.diagnostic_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val section_map = [
    "/* simple-c-layout-section-map-v1 */",
    "#define SIMPLE_LAYOUT_SECTION_dispatch __attribute__((section(\".text.simple.hot.0.dispatch\"), used))",
    "#define SIMPLE_LAYOUT_SECTION_parse __attribute__((section(\".text.simple.hot.1.parse\"), used))"
].join("\n")
val c_source = [
    "#include <stdint.h>",
    "static int dispatch(void) {",
    "  return 1;",
    "}",
    "int parse(void) {",
    "  return dispatch();",
    "}",
    "int main(void) {",
    "  return parse();",
    "}"
].join("\n")

val applied = native_layout_apply_c_section_map(c_source, section_map, true)

expect(applied.enabled).to_equal(true)
expect(applied.applied_count).to_equal(2)
expect(applied.diagnostic_count).to_equal(0)
expect(applied.c_source).to_contain("#define SIMPLE_LAYOUT_SECTION_dispatch __attribute__((section(\".text.simple.hot.0.dispatch\"), used))")
expect(applied.c_source).to_contain("#define SIMPLE_LAYOUT_SECTION_parse __attribute__((section(\".text.simple.hot.1.parse\"), used))")
expect(applied.c_source).to_contain("SIMPLE_LAYOUT_SECTION_dispatch static int dispatch(void) {")
expect(applied.c_source).to_contain("SIMPLE_LAYOUT_SECTION_parse int parse(void) {")
expect(applied.c_source).to_contain("int main(void) {")
```

</details>

#### should leave C unchanged when disabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c_source = "int main(void) {\n  return 0;\n}\n"
val applied = native_layout_apply_c_section_map(c_source, "#define SIMPLE_LAYOUT_SECTION_main __attribute__((section(\".text.simple.hot.0.main\"), used))", false)
expect(applied.enabled).to_equal(false)
expect(applied.applied_count).to_equal(0)
expect(applied.c_source).to_equal(c_source)
```

</details>

#### should fail closed for empty maps and unused mapped symbols

1. "int main
2. "#define SIMPLE LAYOUT SECTION missing   attribute
   - Expected: unused.applied_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = native_layout_apply_c_section_map("int main(void) {\n  return 0;\n}", "", true)
expect(empty.diagnostics).to_contain("empty_section_map")

val unused = native_layout_apply_c_section_map(
    "int main(void) {\n  return 0;\n}",
    "#define SIMPLE_LAYOUT_SECTION_missing __attribute__((section(\".text.simple.hot.0.missing\"), used))",
    true
)
expect(unused.applied_count).to_equal(0)
expect(unused.diagnostics).to_contain("unused_section_map_entry:missing")
```

</details>

#### should collect only section map defines from generated header text

1. "#define SIMPLE LAYOUT SECTION dispatch   attribute
2. ] join
   - Expected: entries.len() equals `1`
   - Expected: entries[0].symbol_name equals `dispatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = native_layout_section_map_entries([
    "/* simple-c-layout-section-map-v1 */",
    "#define OTHER 1",
    "#define SIMPLE_LAYOUT_SECTION_dispatch __attribute__((section(\".text.simple.hot.0.dispatch\"), used))"
].join("\n"))
expect(entries.len()).to_equal(1)
expect(entries[0].symbol_name).to_equal("dispatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compile/feature/native_layout_section_map_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Native Layout Section Map Contract
- section map parsing
- generated C application

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
