# Concurrency Api Misuse Lint Specification

> <details>

<!-- sdn-diagram:id=concurrency_api_misuse_lint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=concurrency_api_misuse_lint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

concurrency_api_misuse_lint_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=concurrency_api_misuse_lint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Concurrency Api Misuse Lint Specification

## Scenarios

### E-PAR-001 task_spawn wrong surface

#### task_spawn imported from std.concurrent.thread

#### flags task_spawn imported from thread path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{task_spawn}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-001")).to_equal(true)
```

</details>

#### message contains 'task_spawn is not part of the OS-thread facade'

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{task_spawn}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "task_spawn is not part of the OS-thread facade")).to_equal(true)
```

</details>

#### negative — correct import

#### does not flag task_spawn from std.nogc_async_mut.thread_pool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.nogc_async_mut.thread_pool.{task_spawn}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-001")).to_equal(false)
```

</details>

### E-PAR-002 numbered concurrency alias

#### thread_spawn2 imported

#### flags thread_spawn2 as a numbered alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{thread_spawn2}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-002")).to_equal(true)
```

</details>

#### message contains 'is a numbered name'

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{thread_spawn2}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "is a numbered name")).to_equal(true)
```

</details>

#### message contains the symbol name thread_spawn2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{thread_spawn2}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "thread_spawn2")).to_equal(true)
```

</details>

#### spawn_isolated2 imported

#### flags spawn_isolated2 as a numbered alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{spawn_isolated2}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-002")).to_equal(true)
```

</details>

#### negative — correct alias name

#### does not flag thread_spawn_with_args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{thread_spawn_with_args}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-002")).to_equal(false)
```

</details>

### E-PAR-003 wrong surface import

#### cooperative_green_spawn from thread surface

#### flags cooperative_green_spawn imported from std.concurrent.thread

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{cooperative_green_spawn}' + "\n\nfn main():\n    val h = cooperative_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(true)
```

</details>

#### message contains the symbol name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{cooperative_green_spawn}' + "\n\nfn main():\n    val h = cooperative_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "cooperative_green_spawn")).to_equal(true)
```

</details>

#### message contains expected owner std.concurrent.cooperative_green

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{cooperative_green_spawn}' + "\n\nfn main():\n    val h = cooperative_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "std.concurrent.cooperative_green")).to_equal(true)
```

</details>

#### multicore_green_spawn from thread surface

#### flags multicore_green_spawn imported from std.concurrent.thread

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{multicore_green_spawn}' + "\n\nfn main():\n    val h = multicore_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(true)
```

</details>

#### thread_spawn from cooperative_green surface

#### flags thread_spawn imported from std.concurrent.cooperative_green

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.cooperative_green.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(true)
```

</details>

#### green_spawn from thread surface

#### flags green_spawn imported from std.concurrent.thread

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{green_spawn}' + "\n\nfn main():\n    val h = green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(true)
```

</details>

#### negative — correct surface

#### does not flag cooperative_green_spawn from correct surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.cooperative_green.{cooperative_green_spawn}' + "\n\nfn main():\n    val h = cooperative_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(false)
```

</details>

#### does not flag thread_spawn from std.concurrent.thread

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(false)
```

</details>

#### does not flag multicore_green_spawn from std.concurrent.multicore_green

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.multicore_green.{multicore_green_spawn}' + "\n\nfn main():\n    val h = multicore_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(false)
```

</details>

### E-PAR-004 invalid argument type

#### thread_spawn called with integer literal

#### flags thread_spawn(42) — integer is not a closure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(42)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### message contains 'pass a closure'

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(42)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "pass a closure")).to_equal(true)
```

</details>

#### green_spawn called with integer literal

#### flags green_spawn(42)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.green_thread.{green_spawn}' + "\n\nfn main():\n    val h = green_spawn(42)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### cooperative_green_spawn called with integer literal

#### flags cooperative_green_spawn(42)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.cooperative_green.{cooperative_green_spawn}' + "\n\nfn main():\n    val h = cooperative_green_spawn(42)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### multicore_green_spawn called with integer literal

#### flags multicore_green_spawn(42)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.multicore_green.{multicore_green_spawn}' + "\n\nfn main():\n    val h = multicore_green_spawn(42)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### multicore_green_set_parallelism called with text arg

#### flags multicore_green_set_parallelism with a text argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.multicore_green.{multicore_green_set_parallelism}' + "\n\nfn main():\n    multicore_green_set_parallelism(\"4\")\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### negative — correct arg types

#### does not flag thread_spawn with closure arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(false)
```

</details>

#### does not flag multicore_green_set_parallelism with integer arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.multicore_green.{multicore_green_set_parallelism}' + "\n\nfn main():\n    multicore_green_set_parallelism(4)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(false)
```

</details>

#### does not flag green_spawn with closure arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.green_thread.{green_spawn}' + "\n\nfn main():\n    val h = green_spawn(\\: 42)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(false)
```

</details>

### E-PAR-004 wrong arity

#### thread_spawn called with two args

#### flags thread_spawn(closure, closure) — two args instead of one

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(\\: 1, \\: 2)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### message contains 'single zero-argument value closure'

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(\\: 1, \\: 2)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "single zero-argument value closure")).to_equal(true)
```

</details>

#### green_spawn called with two args

#### flags green_spawn(closure, closure) — E-PAR-004

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.green_thread.{green_spawn}' + "\n\nfn main():\n    val h = green_spawn(\\: 1, \\: 2)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### cooperative_green_spawn called with two args

#### flags cooperative_green_spawn(closure, closure) — E-PAR-004

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.cooperative_green.{cooperative_green_spawn}' + "\n\nfn main():\n    val h = cooperative_green_spawn(\\: 1, \\: 2)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### multicore_green_spawn called with two args

#### flags multicore_green_spawn(closure, closure) — E-PAR-004

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.multicore_green.{multicore_green_spawn}' + "\n\nfn main():\n    val h = multicore_green_spawn(\\: 1, \\: 2)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### negative — correct arity, does not emit E-PAR-004 for arity

#### does not flag thread_spawn with exactly one arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
# Correct call — no E-PAR-004 at all
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(false)
```

</details>

#### does not flag multicore_green_spawn with one closure arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 'use std.concurrent.multicore_green.{multicore_green_spawn}' + "\n\nfn main():\n    val h = multicore_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(false)
```

</details>

### E-PAR-005 direct rt_pool access

#### rt_pool_submit in extern fn

#### flags extern fn containing rt_pool_submit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "extern fn rt_pool_submit(task: fn() -> void) -> void\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(true)
```

</details>

#### message contains 'internal runtime-pool symbol'

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "extern fn rt_pool_submit(task: fn() -> void) -> void\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "internal runtime-pool symbol")).to_equal(true)
```

</details>

#### message contains the symbol name rt_pool_submit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "extern fn rt_pool_submit(task: fn() -> void) -> void\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "rt_pool_submit")).to_equal(true)
```

</details>

#### rt_pool_join in extern fn

#### flags extern fn containing rt_pool_join

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "extern fn rt_pool_join() -> void\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(true)
```

</details>

#### rt_pool_set_parallelism in extern fn

#### flags extern fn containing rt_pool_set_parallelism

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "extern fn rt_pool_set_parallelism(n: i64) -> void\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(true)
```

</details>

#### rt_pool_get_parallelism in extern fn

#### flags extern fn containing rt_pool_get_parallelism

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "extern fn rt_pool_get_parallelism() -> i64\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(true)
```

</details>

#### rt_pool_is_done in extern fn

#### flags extern fn containing rt_pool_is_done

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "extern fn rt_pool_is_done() -> bool\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(true)
```

</details>

#### negative — only extern fn lines trigger, not call sites or comments

#### does not flag rt_pool_submit in a comment line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "# use rt_pool_submit for low-level access\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(false)
```

</details>

#### does not flag rt_pool_submit as a plain call (no extern fn)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn main():\n    rt_pool_submit(\\: do_work())\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(false)
```

</details>

#### negative — exempt facade path

#### does not flag rt_pool_submit inside the nogc_async_mut facade path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "extern fn rt_pool_submit(task: fn() -> void) -> void\n"
val path = "src/lib/nogc_async_mut/concurrent/multicore_green.spl"
val msgs = check_concurrency_misuse_text(code, path)
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(false)
```

</details>

#### does not flag rt_pool_join inside the gc_async_mut facade path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "extern fn rt_pool_join() -> void\n"
val path = "src/lib/gc_async_mut/concurrent/multicore_green.spl"
val msgs = check_concurrency_misuse_text(code, path)
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/lint/concurrency_api_misuse_lint_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- E-PAR-001 task_spawn wrong surface
- E-PAR-002 numbered concurrency alias
- E-PAR-003 wrong surface import
- E-PAR-004 invalid argument type
- E-PAR-004 wrong arity
- E-PAR-005 direct rt_pool access

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
