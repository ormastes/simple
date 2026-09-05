# config_layers_spec

> Purpose: Prove that std.config core — layered configuration.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# config_layers_spec

Purpose: Prove that std.config core — layered configuration.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/config_core/config_layers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that std.config core — layered configuration.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### std.config core — layered configuration

### layer precedence ranks

#### orders the ten layers from compiled default up to mandatory policy

- read the declared precedence ranks
   - Expected: config_layer_rank("compiled_default") equals `0`
   - Expected: config_layer_rank("vendor") equals `1`
   - Expected: config_layer_rank("machine") equals `2`
   - Expected: config_layer_rank("sysadmin") equals `3`
   - Expected: config_layer_rank("device") equals `4`
   - Expected: config_layer_rank("user") equals `5`
   - Expected: config_layer_rank("profile") equals `6`
   - Expected: config_layer_rank("workspace") equals `7`
   - Expected: config_layer_rank("session") equals `8`
   - Expected: config_layer_rank("mandatory") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-COMMON-001
step("read the declared precedence ranks")
expect(config_layer_rank("compiled_default")).to_equal(0)
expect(config_layer_rank("vendor")).to_equal(1)
expect(config_layer_rank("machine")).to_equal(2)
expect(config_layer_rank("sysadmin")).to_equal(3)
expect(config_layer_rank("device")).to_equal(4)
expect(config_layer_rank("user")).to_equal(5)
expect(config_layer_rank("profile")).to_equal(6)
expect(config_layer_rank("workspace")).to_equal(7)
expect(config_layer_rank("session")).to_equal(8)
expect(config_layer_rank("mandatory")).to_equal(9)
```

</details>

#### rejects an unrecognised layer name

- rejects an unrecognised layer name
- Verify: rejects an unrecognised layer name
   - Expected: config_layer_rank("plugin") equals `-1`
   - Expected: config_layer_names().len() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an unrecognised layer name")
step("Verify: rejects an unrecognised layer name")
expect(config_layer_rank("plugin")).to_equal(-1)
expect(config_layer_names().len()).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

### resolution across layers

#### falls back to the compiled default when no layer contributes

- falls back to the compiled default when no layer contributes
- Verify: falls back to the compiled default when no layer contributes
   - Expected: resolved.value equals `dark`
   - Expected: resolved.layer equals `compiled_default`
   - Expected: resolved.locked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to the compiled default when no layer contributes")
step("Verify: falls back to the compiled default when no layer contributes")
val resolved = config_resolve(theme_field(), [])
expect(resolved.value).to_equal("dark")
expect(resolved.layer).to_equal("compiled_default")
expect(resolved.locked).to_equal(false)
```

</details>

#### lets a user layer override the compiled default

- lets a user layer override the compiled default
- user settings pick the light theme
   - Expected: resolved.value equals `light`
   - Expected: resolved.layer equals `user`
   - Expected: resolved.rank equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets a user layer override the compiled default")
step("user settings pick the light theme")
val entries = [ConfigEntry(key: "theme", value: "light", layer: "user")]
val resolved = config_resolve(theme_field(), entries)
expect(resolved.value).to_equal("light")
expect(resolved.layer).to_equal("user")
expect(resolved.rank).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### lets workspace override user because workspace ranks higher

- lets workspace override user because workspace ranks higher
- Verify: lets workspace override user because workspace ranks higher
   - Expected: config_resolve(theme_field(), entries).value equals `solarized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets workspace override user because workspace ranks higher")
step("Verify: lets workspace override user because workspace ranks higher")
val entries = [
    ConfigEntry(key: "theme", value: "light", layer: "user"),
    ConfigEntry(key: "theme", value: "solarized", layer: "workspace")
]
expect(config_resolve(theme_field(), entries).value).to_equal("solarized")
```

</details>

#### ignores a lower layer even when it appears later in the entry list

- ignores a lower layer even when it appears later in the entry list
- workspace entry is listed before the user entry
   - Expected: resolved.value equals `solarized`
   - Expected: resolved.layer equals `workspace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("ignores a lower layer even when it appears later in the entry list")
step("workspace entry is listed before the user entry")
val entries = [
    ConfigEntry(key: "theme", value: "solarized", layer: "workspace"),
    ConfigEntry(key: "theme", value: "light", layer: "user")
]
val resolved = config_resolve(theme_field(), entries)
expect(resolved.value).to_equal("solarized")
expect(resolved.layer).to_equal("workspace")
```

</details>

#### resolves last-wins between two documents of the same layer

- resolves last-wins between two documents of the same layer
- Verify: resolves last-wins between two documents of the same layer
   - Expected: config_resolve(theme_field(), entries).value equals `solarized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves last-wins between two documents of the same layer")
step("Verify: resolves last-wins between two documents of the same layer")
val entries = [
    ConfigEntry(key: "theme", value: "light", layer: "user"),
    ConfigEntry(key: "theme", value: "solarized", layer: "user")
]
expect(config_resolve(theme_field(), entries).value).to_equal("solarized")
```

</details>

### mandatory policy ceiling

#### overrides a user value even though the user entry comes later

- overrides a user value even though the user entry comes later
- mandatory policy pins the theme, then user tries to change it
   - Expected: resolved.value equals `dark`
   - Expected: resolved.layer equals `mandatory`
   - Expected: resolved.locked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("overrides a user value even though the user entry comes later")
step("mandatory policy pins the theme, then user tries to change it")
val entries = [
    ConfigEntry(key: "theme", value: "dark", layer: "mandatory"),
    ConfigEntry(key: "theme", value: "light", layer: "user")
]
val resolved = config_resolve(theme_field(), entries)
expect(resolved.value).to_equal("dark")
expect(resolved.layer).to_equal("mandatory")
expect(resolved.locked).to_equal(true)
```

</details>

#### overrides the session layer, the highest editable layer

- overrides the session layer, the highest editable layer
- Verify: overrides the session layer, the highest editable layer
   - Expected: config_resolve(theme_field(), entries).value equals `dark`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("overrides the session layer, the highest editable layer")
step("Verify: overrides the session layer, the highest editable layer")
val entries = [
    ConfigEntry(key: "theme", value: "dark", layer: "mandatory"),
    ConfigEntry(key: "theme", value: "solarized", layer: "session")
]
expect(config_resolve(theme_field(), entries).value).to_equal("dark")
```

</details>

#### reports the key as locked through the schema helper

- reports the key as locked through the schema helper
- Verify: reports the key as locked through the schema helper


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports the key as locked through the schema helper")
step("Verify: reports the key as locked through the schema helper")
val entries = [ConfigEntry(key: "theme", value: "dark", layer: "mandatory")]
assert_true(config_is_locked(spec_schema(), entries, "theme"))
assert_false(config_is_locked(spec_schema(), entries, "font_size"))
```

</details>

#### still lets a newer mandatory document replace an older one

- still lets a newer mandatory document replace an older one
- Verify: still lets a newer mandatory document replace an older one
   - Expected: config_resolve(theme_field(), entries).value equals `light`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still lets a newer mandatory document replace an older one")
step("Verify: still lets a newer mandatory document replace an older one")
val entries = [
    ConfigEntry(key: "theme", value: "dark", layer: "mandatory"),
    ConfigEntry(key: "theme", value: "light", layer: "mandatory")
]
expect(config_resolve(theme_field(), entries).value).to_equal("light")
```

</details>

### validation against a descriptor

#### accepts a well-typed integer

- accepts a well-typed integer
- Verify: accepts a well-typed integer
   - Expected: verdict.ok is true
   - Expected: verdict.code equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a well-typed integer")
step("Verify: accepts a well-typed integer")
val verdict = config_validate_value(font_field(), "18")
expect(verdict.ok).to_equal(true)
expect(verdict.code).to_equal("")
```

</details>

#### rejects a non-numeric value for an i64 field

- rejects a non-numeric value for an i64 field
- Verify: rejects a non-numeric value for an i64 field
   - Expected: verdict.ok is false
   - Expected: verdict.code equals `type_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a non-numeric value for an i64 field")
step("Verify: rejects a non-numeric value for an i64 field")
val verdict = config_validate_value(font_field(), "large")
expect(verdict.ok).to_equal(false)
expect(verdict.code).to_equal("type_mismatch")
```

</details>

#### rejects a non-boolean value for a bool field

- rejects a non-boolean value for a bool field
- Verify: rejects a non-boolean value for a bool field
   - Expected: verdict.ok is false
   - Expected: verdict.code equals `type_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a non-boolean value for a bool field")
step("Verify: rejects a non-boolean value for a bool field")
val verdict = config_validate_value(spec_schema()[3], "yes")
expect(verdict.ok).to_equal(false)
expect(verdict.code).to_equal("type_mismatch")
```

</details>

#### accepts the canonical boolean spellings

- accepts the canonical boolean spellings
- Verify: accepts the canonical boolean spellings
   - Expected: config_validate_value(spec_schema()[3], "true").ok is true
   - Expected: config_validate_value(spec_schema()[3], "false").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts the canonical boolean spellings")
step("Verify: accepts the canonical boolean spellings")
expect(config_validate_value(spec_schema()[3], "true").ok).to_equal(true)
expect(config_validate_value(spec_schema()[3], "false").ok).to_equal(true)
```

</details>

#### rejects an integer below the declared minimum

- rejects an integer below the declared minimum
- font_size carries the ported n > 0 guard
   - Expected: verdict.ok is false
   - Expected: verdict.code equals `below_min`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an integer below the declared minimum")
step("font_size carries the ported n > 0 guard")
val verdict = config_validate_value(font_field(), "0")
expect(verdict.ok).to_equal(false)
expect(verdict.code).to_equal("below_min")
```

</details>

#### accepts zero for a field whose minimum is zero

- accepts zero for a field whose minimum is zero
- Verify: accepts zero for a field whose minimum is zero
   - Expected: config_validate_value(spec_schema()[2], "0").ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts zero for a field whose minimum is zero")
step("Verify: accepts zero for a field whose minimum is zero")
expect(config_validate_value(spec_schema()[2], "0").ok).to_equal(true)
```

</details>

#### rejects a value outside the enum option list

- rejects a value outside the enum option list
- Verify: rejects a value outside the enum option list
   - Expected: verdict.ok is false
   - Expected: verdict.code equals `not_in_enum`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a value outside the enum option list")
step("Verify: rejects a value outside the enum option list")
val verdict = config_validate_value(theme_field(), "midnight")
expect(verdict.ok).to_equal(false)
expect(verdict.code).to_equal("not_in_enum")
```

</details>

#### keeps the lower layer when the higher layer value is invalid

- keeps the lower layer when the higher layer value is invalid
- workspace supplies a bad font size; user supplies a good one
   - Expected: resolved.value equals `18`
   - Expected: resolved.layer equals `user`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the lower layer when the higher layer value is invalid")
step("workspace supplies a bad font size; user supplies a good one")
val entries = [
    ConfigEntry(key: "font_size", value: "18", layer: "user"),
    ConfigEntry(key: "font_size", value: "huge", layer: "workspace")
]
val resolved = config_resolve_valid(font_field(), entries)
expect(resolved.value).to_equal("18")
expect(resolved.layer).to_equal("user")
```

</details>

### unknown key detection

#### flags a key the schema does not declare

- flags a key the schema does not declare
- Verify: flags a key the schema does not declare
   - Expected: unknown.len() equals `1`
   - Expected: unknown[0] equals `wombat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flags a key the schema does not declare")
step("Verify: flags a key the schema does not declare")
val unknown = config_unknown_keys(spec_schema(), ["theme", "wombat", "font_size"])
expect(unknown.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(unknown[0]).to_equal("wombat")
```

</details>

#### reports an unknown_key verdict for a key/value pair

- reports an unknown_key verdict for a key/value pair
- Verify: reports an unknown_key verdict for a key/value pair
   - Expected: verdict.ok is false
   - Expected: verdict.code equals `unknown_key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports an unknown_key verdict for a key/value pair")
step("Verify: reports an unknown_key verdict for a key/value pair")
val verdict = config_validate_key_value(spec_schema(), "wombat", "3")
expect(verdict.ok).to_equal(false)
expect(verdict.code).to_equal("unknown_key")
```

</details>

#### accepts every key the schema does declare

- accepts every key the schema does declare
- Verify: accepts every key the schema does declare


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts every key the schema does declare")
step("Verify: accepts every key the schema does declare")
assert_true(config_schema_has_key(spec_schema(), "theme"))
assert_true(config_schema_has_key(spec_schema(), "hover_delay_ms"))
assert_false(config_schema_has_key(spec_schema(), "minimap"))
```

</details>

#### flags unknown keys arriving from a parsed layer document

- flags unknown keys arriving from a parsed layer document
- Verify: flags unknown keys arriving from a parsed layer document
   - Expected: unknown.len() equals `1`
   - Expected: unknown[0] equals `wombat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flags unknown keys arriving from a parsed layer document")
step("Verify: flags unknown keys arriving from a parsed layer document")
val entries = [
    ConfigEntry(key: "theme", value: "light", layer: "user"),
    ConfigEntry(key: "wombat", value: "3", layer: "user")
]
val unknown = config_unknown_entry_keys(spec_schema(), entries)
expect(unknown.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(unknown[0]).to_equal("wombat")
```

</details>

#### collects invalid entries without discarding the valid ones

- collects invalid entries without discarding the valid ones
- Verify: collects invalid entries without discarding the valid ones
   - Expected: config_invalid_entries(spec_schema(), entries).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("collects invalid entries without discarding the valid ones")
step("Verify: collects invalid entries without discarding the valid ones")
val entries = [
    ConfigEntry(key: "theme", value: "midnight", layer: "user"),
    ConfigEntry(key: "font_size", value: "18", layer: "user")
]
expect(config_invalid_entries(spec_schema(), entries).len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

### flat SDN document parsing

#### parses key/value lines and skips comments and blanks

- parses key/value lines and skips comments and blanks
- Verify: parses key/value lines and skips comments and blanks
   - Expected: entries.len() equals `2`
   - Expected: entries[0].key equals `theme`
   - Expected: entries[0].value equals `light`
   - Expected: entries[0].layer equals `user`
   - Expected: entries[1].key equals `font_size`
   - Expected: entries[1].value equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses key/value lines and skips comments and blanks")
step("Verify: parses key/value lines and skips comments and blanks")
val doc = "# user settings\ntheme: light\n\nfont_size: 18\n"
val entries = config_parse_layer(doc, "user")
expect(entries.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(entries[0].key).to_equal("theme")
expect(entries[0].value).to_equal("light")
expect(entries[0].layer).to_equal("user")
expect(entries[1].key).to_equal("font_size")
expect(entries[1].value).to_equal("18")
```

</details>

#### parses a final line that has no trailing newline

- parses a final line that has no trailing newline
- Verify: parses a final line that has no trailing newline
   - Expected: entries.len() equals `1`
   - Expected: entries[0].value equals `solarized`
   - Expected: entries[0].layer equals `session`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses a final line that has no trailing newline")
step("Verify: parses a final line that has no trailing newline")
val entries = config_parse_layer("theme: solarized", "session")
expect(entries.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(entries[0].value).to_equal("solarized")
expect(entries[0].layer).to_equal("session")
```

</details>

#### round-trips entries back to a flat SDN document

- round-trips entries back to a flat SDN document
- Verify: round-trips entries back to a flat SDN document
   - Expected: config_entries_to_sdn(config_parse_layer(doc, "user")) equals `doc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips entries back to a flat SDN document")
step("Verify: round-trips entries back to a flat SDN document")
val doc = "theme: light\nfont_size: 18\n"
expect(config_entries_to_sdn(config_parse_layer(doc, "user"))).to_equal(doc)
```

</details>

#### resolves the effective value from two parsed documents

- resolves the effective value from two parsed documents
- user document then workspace document
   - Expected: config_effective_value(spec_schema(), entries, "theme") equals `light`
   - Expected: config_effective_value(spec_schema(), entries, "font_size") equals `22`
   - Expected: config_effective_value(spec_schema(), entries, "hover_delay_ms") equals `300`
   - Expected: config_effective_value(spec_schema(), entries, "wombat") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves the effective value from two parsed documents")
step("user document then workspace document")
var entries = config_parse_layer("theme: light\nfont_size: 18\n", "user")
val ws = config_parse_layer("font_size: 22\n", "workspace")
var i = 0
while i < ws.len():
    entries.push(ws[i])
    i = i + 1
expect(config_effective_value(spec_schema(), entries, "theme")).to_equal("light")
expect(config_effective_value(spec_schema(), entries, "font_size")).to_equal("22")
expect(config_effective_value(spec_schema(), entries, "hover_delay_ms")).to_equal("300")
expect(config_effective_value(spec_schema(), entries, "wombat")).to_equal("")
```

</details>

#### resolves every schema field in one pass

- resolves every schema field in one pass
- Verify: resolves every schema field in one pass
   - Expected: all.len() equals `4`
   - Expected: all[0].value equals `light`
   - Expected: all[1].value equals `14`
   - Expected: all[2].value equals `300`
   - Expected: all[3].value equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves every schema field in one pass")
step("Verify: resolves every schema field in one pass")
val entries = config_parse_layer("theme: light\n", "user")
val all = config_resolve_all(spec_schema(), entries)
expect(all.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(all[0].value).to_equal("light")
expect(all[1].value).to_equal("14")
expect(all[2].value).to_equal("300")
expect(all[3].value).to_equal("true")
```

</details>

### value conversion helpers

#### parses and formats integers

- parses and formats integers
- Verify: parses and formats integers
   - Expected: config_parse_int("30000") equals `30000`
   - Expected: config_int_to_text(30000) equals `30000`
   - Expected: config_int_to_text(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses and formats integers")
step("Verify: parses and formats integers")
expect(config_parse_int("30000")).to_equal(30000)
expect(config_int_to_text(30000)).to_equal("30000")
expect(config_int_to_text(0)).to_equal("0")
```

</details>

#### formats booleans

- formats booleans
- Verify: formats booleans
   - Expected: config_bool_to_text(true) equals `true`
   - Expected: config_bool_to_text(false) equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("formats booleans")
step("Verify: formats booleans")
expect(config_bool_to_text(true)).to_equal("true")
expect(config_bool_to_text(false)).to_equal("false")
```

</details>

### f64 fields and inline comments (added for the CFG3 consumer)

#### validates f64 text strictly

- validates f64 text strictly
- Verify: validates f64 text strictly
   - Expected: config_validate_value(threshold, "nope").code equals `type_mismatch`
   - Expected: config_validate_value(threshold, ".").code equals `type_mismatch`
   - Expected: config_validate_value(threshold, "1.2.3").code equals `type_mismatch`
   - Expected: config_validate_value(threshold, "").code equals `type_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates f64 text strictly")
step("Verify: validates f64 text strictly")
val threshold = config_f64_field("cpu_threshold", "80.0")
assert_true(config_validate_value(threshold, "70").ok)
assert_true(config_validate_value(threshold, "75.5").ok)
assert_true(config_validate_value(threshold, "-1.25").ok)
expect(config_validate_value(threshold, "nope").code).to_equal("type_mismatch")
expect(config_validate_value(threshold, ".").code).to_equal("type_mismatch")
expect(config_validate_value(threshold, "1.2.3").code).to_equal("type_mismatch")
expect(config_validate_value(threshold, "").code).to_equal("type_mismatch")
```

</details>

#### strips inline comments from values on request

- strips inline comments from values on request
- Verify: strips inline comments from values on request
   - Expected: config_strip_inline_comment("true   # enable it") equals `true`
   - Expected: config_strip_inline_comment("120") equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("strips inline comments from values on request")
step("Verify: strips inline comments from values on request")
expect(config_strip_inline_comment("true   # enable it")).to_equal("true")
expect(config_strip_inline_comment("120")).to_equal("120")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `319e1afb81a2c852df57a12b1e8e515ed13857a932212543f92b05816212a106`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `319e1afb81a2c852df57a12b1e8e515ed13857a932212543f92b05816212a106`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `319e1afb81a2c852df57a12b1e8e515ed13857a932212543f92b05816212a106`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/config_core/config_layers_spec.spl
mirror: doc/06_spec/01_unit/lib/common/config_core/config_layers_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/config_core/config_layers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/config_core/config_layers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/config_core/config_layers_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/config_core/config_layers_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'orders the ten layers from compiled default up to mandatory policy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/config_core/config_layers_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unrecognised layer name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/config_core/config_layers_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'falls back to the compiled default when no layer contributes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
