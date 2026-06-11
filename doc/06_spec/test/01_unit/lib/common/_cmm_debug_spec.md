# Cmm Debug Specification

> 1. print "len: {tokens len

<!-- sdn-diagram:id=_cmm_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=_cmm_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

_cmm_debug_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=_cmm_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cmm Debug Specification

## Scenarios

### CMM stub debug

#### test full line 1

1. print "len: {tokens len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("  SYStem.CPU 78K0R", 1)
print "tokens: {tokens}"
print "len: {tokens.len()}"
expect(tokens.len()).to_be_greater_than(1)
```

</details>

#### test tab line

1. print "len: {tokens len
   - Expected: tokens.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tokens = lex_cmm_line("\tStep", 1)
print "tokens: {tokens}"
print "len: {tokens.len()}"
expect(tokens.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/_cmm_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CMM stub debug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
