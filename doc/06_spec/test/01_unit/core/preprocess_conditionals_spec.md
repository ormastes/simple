# Preprocess Conditionals Specification

> <details>

<!-- sdn-diagram:id=preprocess_conditionals_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=preprocess_conditionals_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

preprocess_conditionals_spec -> core
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=preprocess_conditionals_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Preprocess Conditionals Specification

## Scenarios

### core preprocessor hash directives

#### supports #if/#else/#endif with trailing colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "#if true:\nfn selected() -> i64:\n    return 1\n#else:\nfn broken( -> i64:\n#endif:\nfn main() -> i64:\n    return selected()"
expect(pp_parse_ok(src)).to_equal(true)
```

</details>

#### supports #elif with trailing colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "#if false:\nfn broken_a( -> i64:\n#elif true:\nfn selected() -> i64:\n    return 2\n#else:\nfn broken_b( -> i64:\n#endif\nfn main() -> i64:\n    return selected()"
expect(pp_parse_ok(src)).to_equal(true)
```

</details>

#### supports parenthesized #if with trailing colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = "#if (true):\nfn selected() -> i64:\n    return 7\n#else:\nfn broken( -> i64:\n#endif:\nfn main() -> i64:\n    return selected()"
expect(pp_parse_ok(src)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/core/preprocess_conditionals_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- core preprocessor hash directives

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
