# Label Token Specification

> <details>

<!-- sdn-diagram:id=label_token_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=label_token_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

label_token_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=label_token_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Label Token Specification

## Scenarios

### label tokens for labeled break/continue

<details>
<summary>Advanced: labeled break exits outer loop (via fn return)</summary>

#### labeled break exits outer loop (via fn return)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val found = search_2d(2, 2)
expect(found).to_equal(22)
```

</details>


</details>

#### labeled continue effect (count outer iters not triggering inner)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When inner loop always triggers 'continue outer' at j==1,
# the outer iteration count remains 0
val count = count_outer_iters()
expect(count).to_equal(0)
```

</details>

<details>
<summary>Advanced: unlabeled break only exits inner loop</summary>

#### unlabeled break only exits inner loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 0
for i in 0..3:
    for j in 0..10:
        if j == 2:
            break
    total = total + 1
expect(total).to_equal(3)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lexer/label_token_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- label tokens for labeled break/continue

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
