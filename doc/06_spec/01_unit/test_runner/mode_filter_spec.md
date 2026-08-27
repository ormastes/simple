# Mode Filter Specification

> <details>

<!-- sdn-diagram:id=mode_filter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mode_filter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mode_filter_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mode_filter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mode Filter Specification

## Scenarios

### extract_mode_tags

#### returns empty for no annotations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# just a comment\ndescribe \"foo\":\n    it \"runs\":\n        expect(1).to_equal(1)\n"
expect(_extract_mode_tags(content)).to_equal("")
```

</details>

#### extracts single mode tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @mode: interpreter\ndescribe \"foo\":\n    it \"runs\":\n        expect(1).to_equal(1)\n"
expect(_extract_mode_tags(content)).to_equal("interpreter")
```

</details>

#### extracts multi-mode tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @mode: interpreter, native\ndescribe \"foo\":\n    it \"runs\":\n        expect(1).to_equal(1)\n"
expect(_extract_mode_tags(content)).to_equal("interpreter,native")
```

</details>

#### extracts skip_mode as negated

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# skip-marker-removed_mode: native\ndescribe \"foo\":\n    it \"runs\":\n        expect(1).to_equal(1)\n"
expect(_extract_mode_tags(content)).to_equal("!native")
```

</details>

#### extracts skip_mode with multiple modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# skip-marker-removed_mode: native, smf\ndescribe \"foo\":\n    it \"runs\":\n        expect(1).to_equal(1)\n"
expect(_extract_mode_tags(content)).to_equal("!native,!smf")
```

</details>

### file_mode_matches

#### empty tags match everything

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_file_mode_matches("", "interpreter")).to_equal(true)
expect(_file_mode_matches("", "native")).to_equal(true)
expect(_file_mode_matches("", "smf")).to_equal(true)
```

</details>

#### AllModes always matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_file_mode_matches("interpreter", "all-modes")).to_equal(true)
expect(_file_mode_matches("!native", "all-modes")).to_equal(true)
```

</details>

#### positive tag matches correct mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_file_mode_matches("interpreter", "interpreter")).to_equal(true)
expect(_file_mode_matches("interpreter", "native")).to_equal(false)
```

</details>

#### multi-positive tags match any listed mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_file_mode_matches("interpreter,native", "interpreter")).to_equal(true)
expect(_file_mode_matches("interpreter,native", "native")).to_equal(true)
expect(_file_mode_matches("interpreter,native", "smf")).to_equal(false)
```

</details>

#### skip tag excludes matching mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_file_mode_matches("!native", "native")).to_equal(false)
expect(_file_mode_matches("!native", "interpreter")).to_equal(true)
expect(_file_mode_matches("!native", "smf")).to_equal(true)
```

</details>

#### multiple skip tags exclude all listed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_file_mode_matches("!native,!smf", "native")).to_equal(false)
expect(_file_mode_matches("!native,!smf", "smf")).to_equal(false)
expect(_file_mode_matches("!native,!smf", "interpreter")).to_equal(true)
```

</details>

### file_get_mode_tags

#### returns empty list for no annotations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# nothing here\n"
val tags = _file_get_mode_tags(content)
expect(tags.len()).to_equal(0)
```

</details>

#### extracts mode tags as list

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# @mode: interpreter\n"
val tags = _file_get_mode_tags(content)
expect(tags.len()).to_equal(1)
expect(tags[0]).to_equal("interpreter")
```

</details>

#### extracts skip_mode tags with ! prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "# skip-marker-removed_mode: native\n"
val tags = _file_get_mode_tags(content)
expect(tags.len()).to_equal(1)
expect(tags[0]).to_equal("!native")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/test_runner/mode_filter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- extract_mode_tags
- file_mode_matches
- file_get_mode_tags

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
