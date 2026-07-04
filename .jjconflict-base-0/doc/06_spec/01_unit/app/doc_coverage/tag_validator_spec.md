# Tag Validator Specification

> <details>

<!-- sdn-diagram:id=tag_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tag_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tag_validator_spec -> std
tag_validator_spec -> doc_coverage
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tag_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 58 | 58 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tag Validator Specification

## Scenarios

### validate_tag

#### validates correct coverage tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag("coverage:excellent")
expect(is_valid).to_equal(true)
```

</details>

#### validates correct doc status tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag("doc:missing_sdoctest")
expect(is_valid).to_equal(true)
```

</details>

#### validates correct scope tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag("scope:stdlib")
expect(is_valid).to_equal(true)
```

</details>

#### validates correct api tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag("api:public")
expect(is_valid).to_equal(true)
```

</details>

#### validates tag with numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag("version:v2_0")
expect(is_valid).to_equal(true)
```

</details>

#### rejects tag without colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag("invalid_tag")
expect(is_valid).to_equal(false)
```

</details>

#### rejects tag with multiple colons

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag("category:sub:value")
expect(is_valid).to_equal(false)
```

</details>

#### rejects tag with uppercase letters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag("Coverage:Excellent")
expect(is_valid).to_equal(false)
```

</details>

#### rejects tag with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag("doc:missing sdoctest")
expect(is_valid).to_equal(false)
```

</details>

#### rejects tag with hyphens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag("doc:missing-sdoctest")
expect(is_valid).to_equal(false)
```

</details>

#### rejects empty category

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag(":value")
expect(is_valid).to_equal(false)
```

</details>

#### rejects empty value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag("category:")
expect(is_valid).to_equal(false)
```

</details>

#### rejects tag with special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag("doc:missing@test")
expect(is_valid).to_equal(false)
```

</details>

#### validates tag with all valid characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = validate_tag("abc_123:xyz_789")
expect(is_valid).to_equal(true)
```

</details>

### normalize_tag

#### converts uppercase to lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_tag("Coverage:Excellent")
expect(normalized).to_equal("coverage:excellent")
```

</details>

#### converts spaces to underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_tag("doc:missing sdoctest")
expect(normalized).to_equal("doc:missing_sdoctest")
```

</details>

#### converts hyphens to underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_tag("doc:missing-sdoctest")
expect(normalized).to_equal("doc:missing_sdoctest")
```

</details>

#### removes special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_tag("doc:missing@test!")
expect(normalized).to_equal("doc:missingtest")
```

</details>

#### handles mixed case with spaces and hyphens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_tag("Doc Status:Missing-SDoc Test")
expect(normalized).to_equal("docstatus:missing_sdoctest")
```

</details>

#### preserves already valid tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_tag("coverage:excellent")
expect(normalized).to_equal("coverage:excellent")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_tag("")
expect(normalized).to_equal("")
```

</details>

#### preserves numbers and underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normalized = normalize_tag("version:v2_0")
expect(normalized).to_equal("version:v2_0")
```

</details>

### is_valid_category

#### validates coverage category

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = is_valid_category("coverage")
expect(is_valid).to_equal(true)
```

</details>

#### validates doc category

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = is_valid_category("doc")
expect(is_valid).to_equal(true)
```

</details>

#### validates scope category

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = is_valid_category("scope")
expect(is_valid).to_equal(true)
```

</details>

#### validates api category

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = is_valid_category("api")
expect(is_valid).to_equal(true)
```

</details>

#### validates kind category

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = is_valid_category("kind")
expect(is_valid).to_equal(true)
```

</details>

#### validates group_comment category

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = is_valid_category("group_comment")
expect(is_valid).to_equal(true)
```

</details>

#### validates var_group category

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = is_valid_category("var_group")
expect(is_valid).to_equal(true)
```

</details>

#### rejects unknown category

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = is_valid_category("unknown")
expect(is_valid).to_equal(false)
```

</details>

#### rejects empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_valid = is_valid_category("")
expect(is_valid).to_equal(false)
```

</details>

### extract_category

#### extracts category from valid tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val category = extract_category("coverage:excellent")
expect(category).to_equal("coverage")
```

</details>

#### extracts category with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val category = extract_category("group_comment:detected")
expect(category).to_equal("group_comment")
```

</details>

#### returns empty for tag without colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val category = extract_category("invalid")
expect(category).to_equal("")
```

</details>

#### returns empty for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val category = extract_category("")
expect(category).to_equal("")
```

</details>

#### handles tag with colon at end

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val category = extract_category("category:")
expect(category).to_equal("category")
```

</details>

### extract_value

#### extracts value from valid tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = extract_value("coverage:excellent")
expect(value).to_equal("excellent")
```

</details>

#### extracts value with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = extract_value("doc:missing_sdoctest")
expect(value).to_equal("missing_sdoctest")
```

</details>

#### returns empty for tag without colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = extract_value("invalid")
expect(value).to_equal("")
```

</details>

#### returns empty for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = extract_value("")
expect(value).to_equal("")
```

</details>

#### handles tag with colon at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = extract_value(":value")
expect(value).to_equal("value")
```

</details>

### validate_tag_set

#### validates all valid tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = ["coverage:excellent", "doc:complete", "scope:stdlib"]
val result = validate_tag_set(tags)
val all_valid = result.0
val invalid_tags = result.1

expect(all_valid).to_equal(true)
expect(invalid_tags.len()).to_equal(0)
```

</details>

#### detects single invalid tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = ["coverage:excellent", "Invalid Tag", "scope:stdlib"]
val result = validate_tag_set(tags)
val all_valid = result.0
val invalid_tags = result.1

expect(all_valid).to_equal(false)
expect(invalid_tags.len()).to_equal(1)
expect(invalid_tags[0]).to_equal("Invalid Tag")
```

</details>

#### detects multiple invalid tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = ["no-colon", "Invalid Tag", "valid:tag"]
val result = validate_tag_set(tags)
val all_valid = result.0
val invalid_tags = result.1

expect(all_valid).to_equal(false)
expect(invalid_tags.len()).to_equal(2)
```

</details>

#### handles empty tag set

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = []
val result = validate_tag_set(tags)
val all_valid = result.0
val invalid_tags = result.1

expect(all_valid).to_equal(true)
expect(invalid_tags.len()).to_equal(0)
```

</details>

#### detects tag without value

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = ["coverage:", "doc:complete"]
val result = validate_tag_set(tags)
val all_valid = result.0
val invalid_tags = result.1

expect(all_valid).to_equal(false)
expect(invalid_tags.len()).to_equal(1)
```

</details>

### normalize_tag_set

#### normalizes all tags in set

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = ["Coverage:Excellent", "Doc:Complete", "Scope:StdLib"]
val normalized = normalize_tag_set(tags)

expect(normalized.len()).to_equal(3)
expect(normalized[0]).to_equal("coverage:excellent")
expect(normalized[1]).to_equal("doc:complete")
expect(normalized[2]).to_equal("scope:stdlib")
```

</details>

#### handles tags with spaces and hyphens

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = ["doc:missing sdoctest", "coverage:very-good"]
val normalized = normalize_tag_set(tags)

expect(normalized.len()).to_equal(2)
expect(normalized[0]).to_equal("doc:missing_sdoctest")
expect(normalized[1]).to_equal("coverage:very_good")
```

</details>

#### preserves already normalized tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = ["coverage:excellent", "doc:complete"]
val normalized = normalize_tag_set(tags)

expect(normalized.len()).to_equal(2)
expect(normalized[0]).to_equal("coverage:excellent")
expect(normalized[1]).to_equal("doc:complete")
```

</details>

#### handles empty tag set

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = []
val normalized = normalize_tag_set(tags)

expect(normalized.len()).to_equal(0)
```

</details>

### remove_duplicate_tags

#### removes duplicate tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = ["coverage:excellent", "doc:complete", "coverage:excellent"]
val unique = remove_duplicate_tags(tags)

expect(unique.len()).to_equal(2)

var has_coverage = false
var has_doc = false
for tag in unique:
    if tag == "coverage:excellent":
        has_coverage = true
    if tag == "doc:complete":
        has_doc = true

expect(has_coverage).to_equal(true)
expect(has_doc).to_equal(true)
```

</details>

#### preserves order of first occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = ["scope:stdlib", "doc:complete", "scope:stdlib", "doc:complete"]
val unique = remove_duplicate_tags(tags)

expect(unique.len()).to_equal(2)
expect(unique[0]).to_equal("scope:stdlib")
expect(unique[1]).to_equal("doc:complete")
```

</details>

#### handles no duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = ["coverage:excellent", "doc:complete", "scope:stdlib"]
val unique = remove_duplicate_tags(tags)

expect(unique.len()).to_equal(3)
```

</details>

#### handles all duplicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = ["same:tag", "same:tag", "same:tag"]
val unique = remove_duplicate_tags(tags)

expect(unique.len()).to_equal(1)
expect(unique[0]).to_equal("same:tag")
```

</details>

#### handles empty tag set

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = []
val unique = remove_duplicate_tags(tags)

expect(unique.len()).to_equal(0)
```

</details>

### tag validation integration

#### validates then normalizes invalid tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = "Doc Status:Missing-SDoc Test"
val is_valid_before = validate_tag(tag)
val normalized = normalize_tag(tag)
val is_valid_after = validate_tag(normalized)

expect(is_valid_before).to_equal(false)
expect(is_valid_after).to_equal(true)
```

</details>

#### processes tag set with normalization and deduplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tags: [text] = ["Coverage:Excellent", "doc:complete", "Coverage:Excellent"]
val normalized = normalize_tag_set(tags)
val unique = remove_duplicate_tags(normalized)

expect(unique.len()).to_equal(2)
expect(unique[0]).to_equal("coverage:excellent")
expect(unique[1]).to_equal("doc:complete")
```

</details>

#### validates category after extraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = "coverage:excellent"
val category = extract_category(tag)
val is_valid_cat = is_valid_category(category)

expect(is_valid_cat).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc_coverage/tag_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- validate_tag
- normalize_tag
- is_valid_category
- extract_category
- extract_value
- validate_tag_set
- normalize_tag_set
- remove_duplicate_tags
- tag validation integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 58 |
| Active scenarios | 58 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
