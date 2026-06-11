# Tooling Facade Specification

> 1. Some

<!-- sdn-diagram:id=tooling_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tooling_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tooling_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tooling_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tooling Facade Specification

## Scenarios

### nogc_async_mut src tooling facade

#### re-exports regex utilities

1. Some
   - Expected: m.text equals `128`
   - Expected: m.start equals `4`
2. fail
   - Expected: regex_replace_all(r"\d+", "p50=12 p95=48", "N") equals `pN=N pN=N`
   - Expected: regex_split(r",\s*", "alpha, beta,gamma")[1] equals `beta`
   - Expected: is_valid_email("dev@example.com") is true
   - Expected: extract_numbers("x=7 y=11")[1] equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(regex_is_match(r"\d+", "build 42 passed")).to_equal(true)
val found = regex_find(r"\d+", "run 128 ms")
match found:
    Some(m):
        expect(m.text).to_equal("128")
        expect(m.start).to_equal(4)
    nil:
        fail("regex_find did not return a match for digits")
expect(regex_replace_all(r"\d+", "p50=12 p95=48", "N")).to_equal("pN=N pN=N")
expect(regex_split(r",\s*", "alpha, beta,gamma")[1]).to_equal("beta")
expect(is_valid_email("dev@example.com")).to_equal(true)
expect(extract_numbers("x=7 y=11")[1]).to_equal("11")
```

</details>

#### re-exports easy-fix records

1. fix add replacement
   - Expected: fix.is_safe() is true
   - Expected: fix.replacements.len() as i64 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fix = EasyFix.create("demo.fix", "demo", FixConfidence.Safe)
fix.add_replacement(Replacement.create("file.spl", 1, 2, 1, 2, "x"))
expect(fix.is_safe()).to_equal(true)
expect(fix.replacements.len() as i64).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/src/tooling/tooling_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut src tooling facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
