# Tag Parsing Specification

> <details>

<!-- sdn-diagram:id=tag_parsing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tag_parsing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tag_parsing_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tag_parsing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tag Parsing Specification

## Scenarios

### extract_directive_lines

#### extracts # comment lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @tag:system\nuse std.spec\n# @mode:native"
val lines = _extract_directive_lines(content)
expect(lines.length).to_equal(2)
expect(lines[0]).to_equal("# @tag:system")
expect(lines[1]).to_equal("# @mode:native")
```

</details>

#### extracts directives from inside docstrings

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "\"\"\"\n# @tag:api\n@mode:interpreter\nSome text\n\"\"\"\n# @tag:system"
val lines = _extract_directive_lines(content)
expect(lines.length).to_equal(3)
expect(lines[0]).to_equal("# @tag:api")
expect(lines[1]).to_equal("@mode:interpreter")
expect(lines[2]).to_equal("# @tag:system")
```

</details>

#### ignores non-directive lines in docstrings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "\"\"\"\nSome doc text\n**Category:** Tooling\n\"\"\""
val lines = _extract_directive_lines(content)
expect(lines.length).to_equal(0)
```

</details>

#### handles empty content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = _extract_directive_lines("")
expect(lines.length).to_equal(0)
```

</details>

### extract_tags

#### parses single tag from comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_extract_tags("# @tag:system")).to_equal("system")
```

</details>

#### parses comma-separated tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_extract_tags("# @tag:slow,system")).to_equal("slow,system")
```

</details>

#### parses tag with spaces after comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_extract_tags("# @tag:slow, system")).to_equal("slow,system")
```

</details>

#### parses tag from inside docstring

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "\"\"\"\n@tag:api\n\"\"\""
expect(_extract_tags(content)).to_equal("api")
```

</details>

#### parses tags from both comment and docstring

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @tag:system\n\"\"\"\n@tag:internal\n\"\"\""
expect(_extract_tags(content)).to_equal("system,internal")
```

</details>

#### strips quotes from tag values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_extract_tags("# @tag:\"only-compiled\"")).to_equal("only-compiled")
```

</details>

#### strips brackets and quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_extract_tags("# @tag:[\"only-compiled\"]")).to_equal("only-compiled")
```

</details>

#### excludes skip and pending

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_extract_tags("# @tag:skip")).to_equal("")
expect(_extract_tags("# @tag:pending")).to_equal("")
```

</details>

#### deduplicates tags

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @tag:system\n# @tag:system"
expect(_extract_tags(content)).to_equal("system")
```

</details>

### extract_mode_tags

#### parses mode from comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_extract_mode_tags("# @mode:interpreter")).to_equal("interpreter")
```

</details>

#### parses mode from docstring

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "\"\"\"\n@mode:native\n\"\"\""
expect(_extract_mode_tags(content)).to_equal("native")
```

</details>

#### parses skip_mode with ! prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_extract_mode_tags("# skip-marker-removed_mode:native")).to_equal("!native")
```

</details>

#### parses comma-separated modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_extract_mode_tags("# @mode:interpreter,native")).to_equal("interpreter,native")
```

</details>

#### handles mixed comment and docstring

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @mode:interpreter\n\"\"\"\nskip-marker-removed_mode:native\n\"\"\""
expect(_extract_mode_tags(content)).to_equal("interpreter,!native")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/test_runner/tag_parsing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- extract_directive_lines
- extract_tags
- extract_mode_tags

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
