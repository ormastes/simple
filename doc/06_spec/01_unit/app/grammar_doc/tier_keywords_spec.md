# Tier Keywords Specification

> <details>

<!-- sdn-diagram:id=tier_keywords_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tier_keywords_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tier_keywords_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tier_keywords_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tier Keywords Specification

## Scenarios

### tier_keywords.sdn

#### exists at expected path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = rt_file_exists("doc/06_spec/grammar/tier_keywords.sdn")
expect(found).to_equal(true)
```

</details>

#### is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.len() > 0).to_equal(true)
```

</details>

#### contains keywords.declarations section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("[keywords.declarations]")).to_equal(true)
```

</details>

#### contains keywords.control_flow section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("[keywords.control_flow]")).to_equal(true)
```

</details>

#### contains keywords.expressions section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("[keywords.expressions]")).to_equal(true)
```

</details>

#### contains operators section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("[operators]")).to_equal(true)
```

</details>

#### contains constructs section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("[constructs]")).to_equal(true)
```

</details>

#### classifies fn as seed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("fn = \"seed\"")).to_equal(true)
```

</details>

#### classifies trait as core

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("trait = \"core\"")).to_equal(true)
```

</details>

#### classifies actor as full

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("actor = \"full\"")).to_equal(true)
```

</details>

#### classifies try as full

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("try = \"full\"")).to_equal(true)
```

</details>

#### has treesitter_aspirational section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("[treesitter_aspirational]")).to_equal(true)
```

</details>

### tier_keywords.sdn content validation

#### all seed keywords are present

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
# Check core seed keywords exist
expect(text_content.contains("val = \"seed\"")).to_equal(true)
expect(text_content.contains("var = \"seed\"")).to_equal(true)
expect(text_content.contains("struct = \"seed\"")).to_equal(true)
expect(text_content.contains("if = \"seed\"")).to_equal(true)
expect(text_content.contains("for = \"seed\"")).to_equal(true)
expect(text_content.contains("return = \"seed\"")).to_equal(true)
```

</details>

#### all core keywords are present

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
expect(text_content.contains("loop = \"core\"")).to_equal(true)
expect(text_content.contains("pass = \"core\"")).to_equal(true)
expect(text_content.contains("self = \"core\"")).to_equal(true)
expect(text_content.contains("async = \"core\"")).to_equal(true)
```

</details>

#### contains all three tier values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("doc/06_spec/grammar/tier_keywords.sdn")
val text_content = content ?? ""
# Verify that all three tier values appear in the file
expect(text_content.contains("= \"seed\"")).to_equal(true)
expect(text_content.contains("= \"core\"")).to_equal(true)
expect(text_content.contains("= \"full\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/grammar_doc/tier_keywords_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tier_keywords.sdn
- tier_keywords.sdn content validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
