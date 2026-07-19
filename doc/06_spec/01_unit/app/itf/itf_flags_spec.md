# Itf Flags Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Itf Flags Specification

## Scenarios

### ITF flag extraction

#### _extract_flag

#### extracts flag with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--space", "ENG", "--limit", "10"]
val result = _extract_flag(args, "--space", "")
expect(result).to_equal("ENG")
```

</details>

#### returns default when flag missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--limit", "10"]
val result = _extract_flag(args, "--space", "DEFAULT")
expect(result).to_equal("DEFAULT")
```

</details>

#### handles equals syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--format=json"]
val result = _extract_flag(args, "--format", "text")
expect(result).to_equal("json")
```

</details>

#### extracts last occurrence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--space", "FIRST", "--other", "x", "--space", "SECOND"]
val result = _extract_flag(args, "--space", "")
# Returns first match
expect(result).to_equal("FIRST")
```

</details>

#### _has_flag

#### returns true when flag present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--json", "--web"]
expect(_has_flag(args, "--json")).to_equal(true)
```

</details>

#### returns false when flag absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--json"]
expect(_has_flag(args, "--web")).to_equal(false)
```

</details>

#### handles empty args

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args: [text] = []
expect(_has_flag(args, "--json")).to_equal(false)
```

</details>

#### _positional_args

#### extracts positional args

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["12345", "--format", "json"]
val result = _positional_args(args)
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("12345")
```

</details>

#### handles no flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["hello", "world"]
val result = _positional_args(args)
expect(result.len()).to_equal(2)
```

</details>

#### _remove_flags

#### removes specified flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["view", "--json", "fields", "--web"]
val result = _remove_flags(args, ["--json", "--web"])
expect(result.len()).to_equal(1)
expect(result[0]).to_equal("view")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/itf/itf_flags_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ITF flag extraction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
