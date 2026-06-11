# Concurrency Share Nothing Specification

> <details>

<!-- sdn-diagram:id=concurrency_share_nothing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=concurrency_share_nothing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

concurrency_share_nothing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=concurrency_share_nothing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrency Share Nothing Specification

## Scenarios

### E-PAR-006 share-nothing closure lint

#### green_spawn closure reads module-level var

#### flags green_spawn closure reading a module-level var

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "var shared_total = 0\n\nfn main():\n    val h = green_spawn(\\: shared_total + 1)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(true)
expect(msgs_contain_var(msgs, "shared_total")).to_equal(true)
```

</details>

#### includes 'module-level mutable variable' in the finding

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "var shared_total = 0\n\nfn main():\n    val h = green_spawn(\\: shared_total + 1)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_kind(msgs, "module-level mutable variable")).to_equal(true)
```

</details>

#### cooperative_green_spawn closure writes captured local var

#### flags cooperative_green_spawn closure assigning a captured local var

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn main():\n    var local_count = 0\n    val h = cooperative_green_spawn(\\:\n        local_count = local_count + 1\n        local_count)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(true)
expect(msgs_contain_var(msgs, "local_count")).to_equal(true)
```

</details>

#### includes 'captured mutable variable write' in the finding

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn main():\n    var local_count = 0\n    val h = cooperative_green_spawn(\\:\n        local_count = local_count + 1\n        local_count)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_kind(msgs, "captured mutable variable write")).to_equal(true)
```

</details>

#### multicore_green_spawn closure reads module-level var

#### flags multicore_green_spawn closure reading a module-level var

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "var shared_sum = 0\n\nfn main():\n    val h = multicore_green_spawn(\\: shared_sum + 1)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(true)
expect(msgs_contain_var(msgs, "shared_sum")).to_equal(true)
```

</details>

#### negative cases — no finding expected

#### does not flag a value-only closure (no shared state)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn main():\n    val h = green_spawn(\\: 42)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(false)
```

</details>

#### does not flag reading a module-level val constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "val MAX_RETRIES = 5\n\nfn main():\n    val h = green_spawn(\\: MAX_RETRIES + 1)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(false)
```

</details>

#### does not flag thread_spawn with a module-level var (OS threads are exempt)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "var shared_count = 0\n\nfn main():\n    val h = thread_spawn(\\: shared_count + 1)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(false)
```

</details>

#### does not flag a lambda that only uses its own local variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn main():\n    val h = green_spawn(\\:\n        var x = 10\n        x + 1)\n    h.join()\n"
val msgs = check_share_nothing_text(code)
expect(msgs_contain_code(msgs, "E-PAR-006")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/concurrency_share_nothing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- E-PAR-006 share-nothing closure lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
