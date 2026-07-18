# Language Detect Specification

> <details>

<!-- sdn-diagram:id=language_detect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=language_detect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

language_detect_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=language_detect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Language Detect Specification

## Scenarios

### DetectionResult

#### creates detection result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = DetectionResult.new(language: "simple", confidence: 0.95)
expect result.language == "simple"
expect result.confidence == 0.95
```

</details>

#### ranks by confidence

- DetectionResult new
- DetectionResult new
- DetectionResult new


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val results = [
    DetectionResult.new(language: "rust", confidence: 0.8),
    DetectionResult.new(language: "python", confidence: 0.95),
    DetectionResult.new(language: "simple", confidence: 0.9)
]
# Check that highest confidence result exists
expect results[1].confidence == 0.95
```

</details>

### LanguageDetector

#### detects Python

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val detector = LanguageDetector.new()
check(true)
```

</details>

#### detects Rust

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val detector = LanguageDetector.new()
check(true)
```

</details>

#### detects Simple

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val detector = LanguageDetector.new()
check(true)
```

</details>

#### handles unknown languages

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val detector = LanguageDetector.new()
check(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/parser/language_detect_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DetectionResult
- LanguageDetector

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
