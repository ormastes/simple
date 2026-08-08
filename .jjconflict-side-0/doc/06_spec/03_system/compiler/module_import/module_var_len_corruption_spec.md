# Module Var Len Corruption Specification

> 1.  expect runtime skip gate

<!-- sdn-diagram:id=module_var_len_corruption_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_var_len_corruption_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_var_len_corruption_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_var_len_corruption_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Var Len Corruption Specification

## Scenarios

### Module Array .len() Corruption

#### single .len() call (baseline - should work)

#### calls .len() once on [text] array

1.  expect runtime skip gate
2.  run and check stdout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_stdout("len_once_text.spl", "0")
```

</details>

#### calls .len() once on [i64] array

1.  expect runtime skip gate
2.  run and check stdout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_stdout("len_once_i64.spl", "0")
```

</details>

#### double .len() call (KNOWN BUG - corruption)

#### calls .len() twice on [text] array

1.  expect runtime skip gate
2.  run and check known bug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_known_bug("len_twice_text.spl", ".len() twice on [text] crashes", "0")
```

</details>

#### calls .len() twice on [i64] array

1.  expect runtime skip gate
2.  run and check known bug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_known_bug("len_twice_i64.spl", ".len() twice on [i64] crashes", "0")
```

</details>

#### mixed operations with .len()

#### calls .len() then .push() (KNOWN BUG - single .len() corrupts for all ops)

1.  expect runtime skip gate
2.  run and check known bug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_known_bug("len_then_push.spl", ".len() corrupts array for subsequent .push()", "0")
```

</details>

#### calls .push() then .len()

1.  expect runtime skip gate
2.  run and check known bug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_known_bug("push_then_len.spl", "push_then_len crashes", "1")
```

</details>

#### cross-function and multi-array

#### calls .len() in two separate function invocations

1.  expect runtime skip gate
2.  run and check stdout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_stdout("len_across_functions.spl", "0")
```

</details>

#### calls .len() on different arrays (one per array)

1.  expect runtime skip gate
2.  run and check stdout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_stdout("multiple_arrays_len.spl", "0")
```

</details>

#### workaround - cache .len() in local var

#### caches .len() result and reuses cached value

1.  expect runtime skip gate
2.  run and check stdout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_and_check_stdout("len_cached_workaround.spl", "0")
```

</details>

#### direct run without import (control test)

#### calls .len() twice in directly-run file (KNOWN BUG - also fails without import)

1.  expect runtime skip gate
2.  run and check known bug


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    _expect_runtime_skip_gate()
else:
    # This fixture does NOT import anything - it defines its own array
    # Finding: bug also occurs without import, contradicting initial hypothesis
    _run_and_check_known_bug("direct_run_len_twice.spl", ".len() twice fails even without import", "0")
```

</details>

#### diagnostic - error details on corruption

#### double .len() [text] error mentions type or corruption

1.  expect runtime skip gate
2.  run diag type check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_diag_type_check("len_twice_text.spl", ".len() twice [text]")
```

</details>

#### double .len() [i64] error mentions type or corruption

1.  expect runtime skip gate
2.  run diag type check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_diag_type_check("len_twice_i64.spl", ".len() twice [i64]")
```

</details>

#### compares single vs double .len() behavior

1.  expect runtime skip gate
2.  run diag compare


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    _expect_runtime_skip_gate()
else:
    _run_diag_compare()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/module_import/module_var_len_corruption_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Module Array .len() Corruption

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
