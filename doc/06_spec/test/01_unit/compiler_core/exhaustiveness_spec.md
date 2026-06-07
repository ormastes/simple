# Exhaustiveness Specification

> <details>

<!-- sdn-diagram:id=exhaustiveness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=exhaustiveness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

exhaustiveness_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=exhaustiveness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exhaustiveness Specification

## Scenarios

### Exhaustiveness

#### should expose semantic match exhaustiveness lint warnings

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/35.semantics/lint/match_exhaustiveness.spl")
expect(src.contains("fn check_match_exhaustiveness(decl_indices: [i64]) -> [MatchExhaustivenessWarning]")).to_equal(true)
expect(src.contains("var enum_variants: {text: [text]} = {}")).to_equal(true)
expect(src.contains("val fn_warnings = check_stmts_match(body, fn_name, enum_variants)")).to_equal(true)
expect(src.contains("fn analyze_match(scrutinee: i64, arm_indices: [i64], fn_name: text, enums: {text: [text]}) -> [MatchExhaustivenessWarning]")).to_equal(true)
```

</details>

#### should treat wildcard arms as exhaustive and flag unreachable arms

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/35.semantics/lint/match_exhaustiveness.spl")
expect(src.contains("var has_wildcard = false")).to_equal(true)
expect(src.contains("if pat_name == \"_\"")).to_equal(true)
expect(src.contains("unreachable match arm after wildcard '_'")).to_equal(true)
expect(src.contains("if has_wildcard:")).to_equal(true)
expect(src.contains("return warnings")).to_equal(true)
```

</details>

#### should report missing enum boolean option and result variants

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/35.semantics/lint/match_exhaustiveness.spl")
expect(src.contains("val missing_text = missing.join(\", \")")).to_equal(true)
expect(src.contains("MEXH001")).to_equal(true)
expect(src.contains("MEXH003")).to_equal(true)
expect(src.contains("MEXH005")).to_equal(true)
expect(src.contains("non-exhaustive match on")).to_equal(true)
expect(src.contains("add missing arms or a wildcard")).to_equal(true)
```

</details>

#### should warn when unknown matches lack a default arm

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/35.semantics/lint/match_exhaustiveness.spl")
expect(src.contains("MEXH002")).to_equal(true)
expect(src.contains("match expression has no wildcard/default case")).to_equal(true)
expect(src.contains("add a '_' catch-all arm")).to_equal(true)
```

</details>

#### should keep interpreter match warnings on no matched arm

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval.spl")
expect(src.contains("fn eval_match_expr(eid: i64) -> i64")).to_equal(true)
expect(src.contains("check_match_exhaustive(arm_ids, inferred_type)")).to_equal(true)
expect(src.contains("warning: non-exhaustive match - no arm matched value of type ")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/exhaustiveness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Exhaustiveness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
