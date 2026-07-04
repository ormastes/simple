# Tag Generator Specification

> <details>

<!-- sdn-diagram:id=tag_generator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tag_generator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tag_generator_spec -> std
tag_generator_spec -> doc_coverage
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tag_generator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tag Generator Specification

## Scenarios

### generate_coverage_tag

#### returns excellent for 100% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_coverage_tag(100)
expect(tag).to_equal("coverage:excellent")
```

</details>

#### returns excellent for 95% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_coverage_tag(95)
expect(tag).to_equal("coverage:excellent")
```

</details>

#### returns good for 94% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_coverage_tag(94)
expect(tag).to_equal("coverage:good")
```

</details>

#### returns good for 80% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_coverage_tag(80)
expect(tag).to_equal("coverage:good")
```

</details>

#### returns acceptable for 79% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_coverage_tag(79)
expect(tag).to_equal("coverage:acceptable")
```

</details>

#### returns acceptable for 60% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_coverage_tag(60)
expect(tag).to_equal("coverage:acceptable")
```

</details>

#### returns poor for 59% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_coverage_tag(59)
expect(tag).to_equal("coverage:poor")
```

</details>

#### returns poor for 40% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_coverage_tag(40)
expect(tag).to_equal("coverage:poor")
```

</details>

#### returns insufficient for 39% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_coverage_tag(39)
expect(tag).to_equal("coverage:insufficient")
```

</details>

#### returns insufficient for 0% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_coverage_tag(0)
expect(tag).to_equal("coverage:insufficient")
```

</details>

### generate_doc_status_tags

#### returns complete for fully documented public function

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_function("foo", "/src/std/test.spl", true, true, true, true, true)
val tags = generate_doc_status_tags(item)

expect(tags.len()).to_equal(1)
expect(tags[0]).to_equal("doc:complete")
```

</details>

#### returns incomplete for public function missing sdoctest

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_function("foo", "/src/std/test.spl", true, true, false, true, true)
val tags = generate_doc_status_tags(item)

var has_incomplete = false
var has_missing_sdoctest = false

for tag in tags:
    if tag == "doc:incomplete":
        has_incomplete = true
    if tag == "doc:missing_sdoctest":
        has_missing_sdoctest = true

expect(has_incomplete).to_equal(true)
expect(has_missing_sdoctest).to_equal(true)
```

</details>

#### returns incomplete for function missing inline comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_function("foo", "/src/std/test.spl", false, true, true, true, true)
val tags = generate_doc_status_tags(item)

var has_incomplete = false
var has_missing_inline = false

for tag in tags:
    if tag == "doc:incomplete":
        has_incomplete = true
    if tag == "doc:missing_inline_comment":
        has_missing_inline = true

expect(has_incomplete).to_equal(true)
expect(has_missing_inline).to_equal(true)
```

</details>

#### returns complete for private function with inline or docstring

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_function("_private", "/src/std/test.spl", true, false, false, false, false)
val tags = generate_doc_status_tags(item)

expect(tags.len()).to_equal(1)
expect(tags[0]).to_equal("doc:complete")
```

</details>

#### returns incomplete for completely undocumented function

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_function("foo", "/src/std/test.spl", false, false, false, true, true)
val tags = generate_doc_status_tags(item)

var has_incomplete = false
var has_missing_inline = false
var has_missing_sdoctest = false

for tag in tags:
    if tag == "doc:incomplete":
        has_incomplete = true
    if tag == "doc:missing_inline_comment":
        has_missing_inline = true
    if tag == "doc:missing_sdoctest":
        has_missing_sdoctest = true

expect(has_incomplete).to_equal(true)
expect(has_missing_inline).to_equal(true)
expect(has_missing_sdoctest).to_equal(true)
```

</details>

#### handles struct with docstring as complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_struct("Point", "/src/std/test.spl", true)
val tags = generate_doc_status_tags(item)

expect(tags[0]).to_equal("doc:complete")
```

</details>

#### handles struct without docstring as incomplete

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_struct("Point", "/src/std/test.spl", false)
val tags = generate_doc_status_tags(item)

var has_incomplete = false
var has_missing_inline = false

for tag in tags:
    if tag == "doc:incomplete":
        has_incomplete = true
    if tag == "doc:missing_inline_comment":
        has_missing_inline = true

expect(has_incomplete).to_equal(true)
expect(has_missing_inline).to_equal(true)
```

</details>

### generate_scope_tag

#### returns stdlib for src/std/ path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_scope_tag("/home/user/project/src/std/string.spl")
expect(tag).to_equal("scope:stdlib")
```

</details>

#### returns core for src/core/ path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_scope_tag("/home/user/project/src/core/parser.spl")
expect(tag).to_equal("scope:core")
```

</details>

#### returns lib for src/lib/ path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_scope_tag("/home/user/project/src/lib/database/core.spl")
expect(tag).to_equal("scope:lib")
```

</details>

#### returns app for src/app/ path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_scope_tag("/home/user/project/src/app/cli/main.spl")
expect(tag).to_equal("scope:app")
```

</details>

#### returns compiler for src/compiler/ path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_scope_tag("/home/user/project/src/compiler/backend/native.spl")
expect(tag).to_equal("scope:compiler")
```

</details>

#### returns unknown for unrecognized path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_scope_tag("/home/user/other/file.spl")
expect(tag).to_equal("scope:unknown")
```

</details>

#### handles relative paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_scope_tag("src/std/spec.spl")
expect(tag).to_equal("scope:stdlib")
```

</details>

### generate_api_tag

#### returns public for exported function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_api_tag(true)
expect(tag).to_equal("api:public")
```

</details>

#### returns internal for non-exported function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tag = generate_api_tag(false)
expect(tag).to_equal("api:internal")
```

</details>

### generate_all_tags

#### generates all tags for fully documented public function

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_function("add", "/home/user/src/std/math.spl", true, true, true, true, true)
val tags = generate_all_tags(item)

var has_scope = false
var has_api = false
var has_doc = false
var has_kind = false

for tag in tags:
    if tag == "scope:stdlib":
        has_scope = true
    if tag == "api:public":
        has_api = true
    if tag == "doc:complete":
        has_doc = true
    if tag == "kind:function":
        has_kind = true

expect(has_scope).to_equal(true)
expect(has_api).to_equal(true)
expect(has_doc).to_equal(true)
expect(has_kind).to_equal(true)
```

</details>

#### generates correct tags for undocumented internal function

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_function("_helper", "/home/user/src/app/cli/main.spl", false, false, false, false, false)
val tags = generate_all_tags(item)

var has_scope_app = false
var has_api_internal = false
var has_kind_func = false

for tag in tags:
    if tag == "scope:app":
        has_scope_app = true
    if tag == "api:internal":
        has_api_internal = true
    if tag == "kind:function":
        has_kind_func = true

expect(has_scope_app).to_equal(true)
expect(has_api_internal).to_equal(true)
expect(has_kind_func).to_equal(true)
```

</details>

#### includes multiple doc status tags when appropriate

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_function("foo", "/home/user/src/core/lexer.spl", false, false, false, true, true)
val tags = generate_all_tags(item)

var has_incomplete = false
var has_missing_inline = false
var has_missing_sdoctest = false

for tag in tags:
    if tag == "doc:incomplete":
        has_incomplete = true
    if tag == "doc:missing_inline_comment":
        has_missing_inline = true
    if tag == "doc:missing_sdoctest":
        has_missing_sdoctest = true

expect(has_incomplete).to_equal(true)
expect(has_missing_inline).to_equal(true)
expect(has_missing_sdoctest).to_equal(true)
```

</details>

### filter_items_by_tag

#### filters items by scope tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item1 = create_test_function("foo", "/src/std/test.spl", true, true, true, true, true)
val item2 = create_test_function("bar", "/src/core/test.spl", true, true, true, true, true)
val item3 = create_test_function("baz", "/src/std/other.spl", true, true, true, true, true)

val items: [DocItem] = [item1, item2, item3]
val filtered = filter_items_by_tag(items, "scope:stdlib")

expect(filtered.len()).to_equal(2)
```

</details>

#### filters items by doc status tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item1 = create_test_function("foo", "/src/std/test.spl", true, true, true, true, true)
val item2 = create_test_function("bar", "/src/std/test.spl", false, false, false, true, true)
val item3 = create_test_function("baz", "/src/std/test.spl", true, true, false, true, true)

val items: [DocItem] = [item1, item2, item3]
val filtered = filter_items_by_tag(items, "doc:complete")

expect(filtered.len()).to_equal(1)
```

</details>

#### returns empty array when no items match

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item1 = create_test_function("foo", "/src/std/test.spl", true, true, true, true, true)
val item2 = create_test_function("bar", "/src/std/test.spl", true, true, true, true, true)

val items: [DocItem] = [item1, item2]
val filtered = filter_items_by_tag(items, "scope:compiler")

expect(filtered.len()).to_equal(0)
```

</details>

#### handles empty input array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items: [DocItem] = []
val filtered = filter_items_by_tag(items, "scope:stdlib")

expect(filtered.len()).to_equal(0)
```

</details>

### get_unique_tags

#### returns unique tags from multiple items

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item1 = create_test_function("foo", "/src/std/test.spl", true, true, true, true, true)
val item2 = create_test_function("bar", "/src/core/test.spl", false, false, false, true, true)

val items: [DocItem] = [item1, item2]
val tags = get_unique_tags(items)

var has_stdlib = false
var has_core = false

for tag in tags:
    if tag == "scope:stdlib":
        has_stdlib = true
    if tag == "scope:core":
        has_core = true

expect(has_stdlib).to_equal(true)
expect(has_core).to_equal(true)
```

</details>

#### does not duplicate tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item1 = create_test_function("foo", "/src/std/test.spl", true, true, true, true, true)
val item2 = create_test_function("bar", "/src/std/test.spl", true, true, true, true, true)

val items: [DocItem] = [item1, item2]
val tags = get_unique_tags(items)

var count_stdlib = 0
for tag in tags:
    if tag == "scope:stdlib":
        count_stdlib = count_stdlib + 1

expect(count_stdlib).to_equal(1)
```

</details>

#### handles empty input array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items: [DocItem] = []
val tags = get_unique_tags(items)

expect(tags.len()).to_equal(0)
```

</details>

#### includes all tag categories

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = create_test_function("foo", "/src/std/test.spl", true, true, true, true, true)
val items: [DocItem] = [item]
val tags = get_unique_tags(items)

var has_scope = false
var has_api = false
var has_doc = false
var has_kind = false

for tag in tags:
    if tag.starts_with("scope:"):
        has_scope = true
    if tag.starts_with("api:"):
        has_api = true
    if tag.starts_with("doc:"):
        has_doc = true
    if tag.starts_with("kind:"):
        has_kind = true

expect(has_scope).to_equal(true)
expect(has_api).to_equal(true)
expect(has_doc).to_equal(true)
expect(has_kind).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc_coverage/tag_generator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- generate_coverage_tag
- generate_doc_status_tags
- generate_scope_tag
- generate_api_tag
- generate_all_tags
- filter_items_by_tag
- get_unique_tags

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
