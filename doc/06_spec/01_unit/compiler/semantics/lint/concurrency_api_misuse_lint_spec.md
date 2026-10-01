# Concurrency Api Misuse Lint Specification

> Tests covering E-PAR-001 task_spawn wrong surface, E-PAR-002 numbered concurrency alias, E-PAR-003 wrong surface import, E-PAR-004 invalid argument type, E-PAR-004 wrong arity, E-PAR-005 direct rt_pool access.

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

- flags task_spawn imported from thread path
   - Expected: tc_has_code(msgs, "E-PAR-001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags task_spawn imported from thread path")
val code = 'use std.concurrent.thread.{task_spawn}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-001")).to_equal(true)
```

</details>

#### message contains 'task_spawn is not part of the OS-thread facade'

- message contains 'task_spawn is not part of the OS-thread facade'
   - Expected: tc_any_contains(msgs, "task_spawn is not part of the OS-thread facade") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message contains 'task_spawn is not part of the OS-thread facade'")
val code = 'use std.concurrent.thread.{task_spawn}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "task_spawn is not part of the OS-thread facade")).to_equal(true)
```

</details>

#### negative — correct import

#### does not flag task_spawn from std.nogc_async_mut.thread_pool

- does not flag task_spawn from std.nogc_async_mut.thread_pool
   - Expected: tc_has_code(msgs, "E-PAR-001") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag task_spawn from std.nogc_async_mut.thread_pool")
val code = 'use std.nogc_async_mut.thread_pool.{task_spawn}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-001")).to_equal(false)
```

</details>

### E-PAR-002 numbered concurrency alias

#### thread_spawn2 imported

#### flags thread_spawn2 as a numbered alias

- flags thread_spawn2 as a numbered alias
   - Expected: tc_has_code(msgs, "E-PAR-002") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags thread_spawn2 as a numbered alias")
val code = 'use std.concurrent.thread.{thread_spawn2}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-002")).to_equal(true)
```

</details>

#### message contains 'is a numbered name'

- message contains 'is a numbered name'
   - Expected: tc_any_contains(msgs, "is a numbered name") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message contains 'is a numbered name'")
val code = 'use std.concurrent.thread.{thread_spawn2}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "is a numbered name")).to_equal(true)
```

</details>

#### message contains the symbol name thread_spawn2

- message contains the symbol name thread_spawn2
   - Expected: tc_any_contains(msgs, "thread_spawn2") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message contains the symbol name thread_spawn2")
val code = 'use std.concurrent.thread.{thread_spawn2}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "thread_spawn2")).to_equal(true)
```

</details>

#### spawn_isolated2 imported

#### flags spawn_isolated2 as a numbered alias

- flags spawn_isolated2 as a numbered alias
   - Expected: tc_has_code(msgs, "E-PAR-002") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags spawn_isolated2 as a numbered alias")
val code = 'use std.concurrent.thread.{spawn_isolated2}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-002")).to_equal(true)
```

</details>

#### negative — correct alias name

#### does not flag thread_spawn_with_args

- does not flag thread_spawn_with_args
   - Expected: tc_has_code(msgs, "E-PAR-002") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag thread_spawn_with_args")
val code = 'use std.concurrent.thread.{thread_spawn_with_args}' + "\n\nfn main():\n    val x = 1\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-002")).to_equal(false)
```

</details>

### E-PAR-003 wrong surface import

#### cooperative_green_spawn from thread surface

#### flags cooperative_green_spawn imported from std.concurrent.thread

- flags cooperative_green_spawn imported from std.concurrent.thread
   - Expected: tc_has_code(msgs, "E-PAR-003") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags cooperative_green_spawn imported from std.concurrent.thread")
val code = 'use std.concurrent.thread.{cooperative_green_spawn}' + "\n\nfn main():\n    val h = cooperative_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(true)
```

</details>

#### message contains the symbol name

- message contains the symbol name
   - Expected: tc_any_contains(msgs, "cooperative_green_spawn") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message contains the symbol name")
val code = 'use std.concurrent.thread.{cooperative_green_spawn}' + "\n\nfn main():\n    val h = cooperative_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "cooperative_green_spawn")).to_equal(true)
```

</details>

#### message contains expected owner std.concurrent.cooperative_green

- message contains expected owner std.concurrent.cooperative_green
   - Expected: tc_any_contains(msgs, "std.concurrent.cooperative_green") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message contains expected owner std.concurrent.cooperative_green")
val code = 'use std.concurrent.thread.{cooperative_green_spawn}' + "\n\nfn main():\n    val h = cooperative_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "std.concurrent.cooperative_green")).to_equal(true)
```

</details>

#### multicore_green_spawn from thread surface

#### flags multicore_green_spawn imported from std.concurrent.thread

- flags multicore_green_spawn imported from std.concurrent.thread
   - Expected: tc_has_code(msgs, "E-PAR-003") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags multicore_green_spawn imported from std.concurrent.thread")
val code = 'use std.concurrent.thread.{multicore_green_spawn}' + "\n\nfn main():\n    val h = multicore_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(true)
```

</details>

#### thread_spawn from cooperative_green surface

#### flags thread_spawn imported from std.concurrent.cooperative_green

- flags thread_spawn imported from std.concurrent.cooperative_green
   - Expected: tc_has_code(msgs, "E-PAR-003") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags thread_spawn imported from std.concurrent.cooperative_green")
val code = 'use std.concurrent.cooperative_green.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(true)
```

</details>

#### green_spawn from thread surface

#### flags green_spawn imported from std.concurrent.thread

- flags green_spawn imported from std.concurrent.thread
   - Expected: tc_has_code(msgs, "E-PAR-003") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags green_spawn imported from std.concurrent.thread")
val code = 'use std.concurrent.thread.{green_spawn}' + "\n\nfn main():\n    val h = green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(true)
```

</details>

#### negative — correct surface

#### does not flag cooperative_green_spawn from correct surface

- does not flag cooperative_green_spawn from correct surface
   - Expected: tc_has_code(msgs, "E-PAR-003") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag cooperative_green_spawn from correct surface")
val code = 'use std.concurrent.cooperative_green.{cooperative_green_spawn}' + "\n\nfn main():\n    val h = cooperative_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(false)
```

</details>

#### does not flag thread_spawn from std.concurrent.thread

- does not flag thread_spawn from std.concurrent.thread
   - Expected: tc_has_code(msgs, "E-PAR-003") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag thread_spawn from std.concurrent.thread")
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(false)
```

</details>

#### does not flag multicore_green_spawn from std.concurrent.multicore_green

- does not flag multicore_green_spawn from std.concurrent.multicore_green
   - Expected: tc_has_code(msgs, "E-PAR-003") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag multicore_green_spawn from std.concurrent.multicore_green")
val code = 'use std.concurrent.multicore_green.{multicore_green_spawn}' + "\n\nfn main():\n    val h = multicore_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-003")).to_equal(false)
```

</details>

### E-PAR-004 invalid argument type

#### thread_spawn called with integer literal

#### flags thread_spawn(42) — integer is not a closure

- flags thread_spawn(42) — integer is not a closure
   - Expected: tc_has_code(msgs, "E-PAR-004") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags thread_spawn(42) — integer is not a closure")
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(42)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### message contains 'pass a closure'

- message contains 'pass a closure'
   - Expected: tc_any_contains(msgs, "pass a closure") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message contains 'pass a closure'")
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(42)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "pass a closure")).to_equal(true)
```

</details>

#### green_spawn called with integer literal

#### flags green_spawn(42)

- flags green_spawn(42)
   - Expected: tc_has_code(msgs, "E-PAR-004") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags green_spawn(42)")
val code = 'use std.concurrent.green_thread.{green_spawn}' + "\n\nfn main():\n    val h = green_spawn(42)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### cooperative_green_spawn called with integer literal

#### flags cooperative_green_spawn(42)

- flags cooperative_green_spawn(42)
   - Expected: tc_has_code(msgs, "E-PAR-004") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags cooperative_green_spawn(42)")
val code = 'use std.concurrent.cooperative_green.{cooperative_green_spawn}' + "\n\nfn main():\n    val h = cooperative_green_spawn(42)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### multicore_green_spawn called with integer literal

#### flags multicore_green_spawn(42)

- flags multicore_green_spawn(42)
   - Expected: tc_has_code(msgs, "E-PAR-004") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags multicore_green_spawn(42)")
val code = 'use std.concurrent.multicore_green.{multicore_green_spawn}' + "\n\nfn main():\n    val h = multicore_green_spawn(42)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### multicore_green_set_parallelism called with text arg

#### flags multicore_green_set_parallelism with a text argument

- flags multicore_green_set_parallelism with a text argument
   - Expected: tc_has_code(msgs, "E-PAR-004") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags multicore_green_set_parallelism with a text argument")
val code = 'use std.concurrent.multicore_green.{multicore_green_set_parallelism}' + "\n\nfn main():\n    multicore_green_set_parallelism(\"4\")\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### negative — correct arg types

#### does not flag thread_spawn with closure arg

- does not flag thread_spawn with closure arg
   - Expected: tc_has_code(msgs, "E-PAR-004") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag thread_spawn with closure arg")
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(false)
```

</details>

#### does not flag multicore_green_set_parallelism with integer arg

- does not flag multicore_green_set_parallelism with integer arg
   - Expected: tc_has_code(msgs, "E-PAR-004") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag multicore_green_set_parallelism with integer arg")
val code = 'use std.concurrent.multicore_green.{multicore_green_set_parallelism}' + "\n\nfn main():\n    multicore_green_set_parallelism(4)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(false)
```

</details>

#### does not flag green_spawn with closure arg

- does not flag green_spawn with closure arg
   - Expected: tc_has_code(msgs, "E-PAR-004") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag green_spawn with closure arg")
val code = 'use std.concurrent.green_thread.{green_spawn}' + "\n\nfn main():\n    val h = green_spawn(\\: 42)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(false)
```

</details>

### E-PAR-004 wrong arity

#### thread_spawn called with two args

#### flags thread_spawn(closure, closure) — two args instead of one

- flags thread_spawn(closure, closure) — two args instead of one
   - Expected: tc_has_code(msgs, "E-PAR-004") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags thread_spawn(closure, closure) — two args instead of one")
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(\\: 1, \\: 2)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### message contains 'single zero-argument value closure'

- message contains 'single zero-argument value closure'
   - Expected: tc_any_contains(msgs, "single zero-argument value closure") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message contains 'single zero-argument value closure'")
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(\\: 1, \\: 2)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "single zero-argument value closure")).to_equal(true)
```

</details>

#### green_spawn called with two args

#### flags green_spawn(closure, closure) — E-PAR-004

- flags green_spawn(closure, closure) — E-PAR-004
   - Expected: tc_has_code(msgs, "E-PAR-004") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags green_spawn(closure, closure) — E-PAR-004")
val code = 'use std.concurrent.green_thread.{green_spawn}' + "\n\nfn main():\n    val h = green_spawn(\\: 1, \\: 2)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### cooperative_green_spawn called with two args

#### flags cooperative_green_spawn(closure, closure) — E-PAR-004

- flags cooperative_green_spawn(closure, closure) — E-PAR-004
   - Expected: tc_has_code(msgs, "E-PAR-004") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags cooperative_green_spawn(closure, closure) — E-PAR-004")
val code = 'use std.concurrent.cooperative_green.{cooperative_green_spawn}' + "\n\nfn main():\n    val h = cooperative_green_spawn(\\: 1, \\: 2)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### multicore_green_spawn called with two args

#### flags multicore_green_spawn(closure, closure) — E-PAR-004

- flags multicore_green_spawn(closure, closure) — E-PAR-004
   - Expected: tc_has_code(msgs, "E-PAR-004") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags multicore_green_spawn(closure, closure) — E-PAR-004")
val code = 'use std.concurrent.multicore_green.{multicore_green_spawn}' + "\n\nfn main():\n    val h = multicore_green_spawn(\\: 1, \\: 2)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(true)
```

</details>

#### negative — correct arity, does not emit E-PAR-004 for arity

#### does not flag thread_spawn with exactly one arg

- does not flag thread_spawn with exactly one arg
   - Expected: tc_has_code(msgs, "E-PAR-004") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag thread_spawn with exactly one arg")
val code = 'use std.concurrent.thread.{thread_spawn}' + "\n\nfn main():\n    val h = thread_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
# Correct call — no E-PAR-004 at all
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(false)
```

</details>

#### does not flag multicore_green_spawn with one closure arg

- does not flag multicore_green_spawn with one closure arg
   - Expected: tc_has_code(msgs, "E-PAR-004") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag multicore_green_spawn with one closure arg")
val code = 'use std.concurrent.multicore_green.{multicore_green_spawn}' + "\n\nfn main():\n    val h = multicore_green_spawn(\\: 1)\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-004")).to_equal(false)
```

</details>

### E-PAR-005 direct rt_pool access

#### rt_pool_submit in extern fn

#### flags extern fn containing rt_pool_submit

- flags extern fn containing rt_pool_submit
   - Expected: tc_has_code(msgs, "E-PAR-005") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags extern fn containing rt_pool_submit")
val code = "extern fn rt_pool_submit(task: fn() -> void) -> void\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(true)
```

</details>

#### message contains 'internal runtime-pool symbol'

- message contains 'internal runtime-pool symbol'
   - Expected: tc_any_contains(msgs, "internal runtime-pool symbol") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message contains 'internal runtime-pool symbol'")
val code = "extern fn rt_pool_submit(task: fn() -> void) -> void\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "internal runtime-pool symbol")).to_equal(true)
```

</details>

#### message contains the symbol name rt_pool_submit

- message contains the symbol name rt_pool_submit
   - Expected: tc_any_contains(msgs, "rt_pool_submit") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("message contains the symbol name rt_pool_submit")
val code = "extern fn rt_pool_submit(task: fn() -> void) -> void\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_any_contains(msgs, "rt_pool_submit")).to_equal(true)
```

</details>

#### rt_pool_join in extern fn

#### flags extern fn containing rt_pool_join

- flags extern fn containing rt_pool_join
   - Expected: tc_has_code(msgs, "E-PAR-005") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags extern fn containing rt_pool_join")
val code = "extern fn rt_pool_join() -> void\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(true)
```

</details>

#### rt_pool_set_parallelism in extern fn

#### flags extern fn containing rt_pool_set_parallelism

- flags extern fn containing rt_pool_set_parallelism
   - Expected: tc_has_code(msgs, "E-PAR-005") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags extern fn containing rt_pool_set_parallelism")
val code = "extern fn rt_pool_set_parallelism(n: i64) -> void\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(true)
```

</details>

#### rt_pool_get_parallelism in extern fn

#### flags extern fn containing rt_pool_get_parallelism

- flags extern fn containing rt_pool_get_parallelism
   - Expected: tc_has_code(msgs, "E-PAR-005") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags extern fn containing rt_pool_get_parallelism")
val code = "extern fn rt_pool_get_parallelism() -> i64\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(true)
```

</details>

#### rt_pool_is_done in extern fn

#### flags extern fn containing rt_pool_is_done

- flags extern fn containing rt_pool_is_done
   - Expected: tc_has_code(msgs, "E-PAR-005") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags extern fn containing rt_pool_is_done")
val code = "extern fn rt_pool_is_done() -> bool\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(true)
```

</details>

#### negative — only extern fn lines trigger, not call sites or comments

#### does not flag rt_pool_submit in a comment line

- does not flag rt_pool_submit in a comment line
   - Expected: tc_has_code(msgs, "E-PAR-005") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag rt_pool_submit in a comment line")
val code = "# use rt_pool_submit for low-level access\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(false)
```

</details>

#### does not flag rt_pool_submit as a plain call (no extern fn)

- does not flag rt_pool_submit as a plain call (no extern fn)
   - Expected: tc_has_code(msgs, "E-PAR-005") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag rt_pool_submit as a plain call (no extern fn)")
val code = "fn main():\n    rt_pool_submit(\\: do_work())\n"
val msgs = check_concurrency_misuse_text(code, "")
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(false)
```

</details>

#### negative — exempt facade path

#### does not flag rt_pool_submit inside the nogc_async_mut facade path

- does not flag rt_pool_submit inside the nogc_async_mut facade path
   - Expected: tc_has_code(msgs, "E-PAR-005") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag rt_pool_submit inside the nogc_async_mut facade path")
val code = "extern fn rt_pool_submit(task: fn() -> void) -> void\n"
val path = "src/lib/nogc_async_mut/concurrent/multicore_green.spl"
val msgs = check_concurrency_misuse_text(code, path)
expect(tc_has_code(msgs, "E-PAR-005")).to_equal(false)
```

</details>

#### does not flag rt_pool_join inside the gc_async_mut facade path

- does not flag rt_pool_join inside the gc_async_mut facade path
   - Expected: tc_has_code(msgs, "E-PAR-005") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag rt_pool_join inside the gc_async_mut facade path")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering E-PAR-001 task_spawn wrong surface, E-PAR-002 numbered concurrency alias, E-PAR-003 wrong surface import, E-PAR-004 invalid argument type, E-PAR-004 wrong arity, E-PAR-005 direct rt_pool access.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e8b2bf077cd9a0893d0979c0cfb425c4fe63eb2182600f4e79f16fbb951072c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e8b2bf077cd9a0893d0979c0cfb425c4fe63eb2182600f4e79f16fbb951072c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e8b2bf077cd9a0893d0979c0cfb425c4fe63eb2182600f4e79f16fbb951072c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/semantics/lint/concurrency_api_misuse_lint_spec.spl
mirror: doc/06_spec/01_unit/compiler/semantics/lint/concurrency_api_misuse_lint_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/semantics/lint/concurrency_api_misuse_lint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/semantics/lint/concurrency_api_misuse_lint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/semantics/lint/concurrency_api_misuse_lint_spec.spl:342:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags task_spawn imported from thread path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/concurrency_api_misuse_lint_spec.spl:349:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'message contains 'task_spawn is not part of the OS-thread facade'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/semantics/lint/concurrency_api_misuse_lint_spec.spl:357:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag task_spawn from std.nogc_async_mut.thread_pool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
