# Module System Specification

> 1. write source

<!-- sdn-diagram:id=module_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module System Specification

## Scenarios

### Module System - Import Syntax

#### use module imports a single function

1. write source
2. write source
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `pong`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "/tmp/sml_sys_mod_single.spl"
val main_path = "/tmp/sml_sys_main_single.spl"

val mod_src = "fn ping() -> text:" + NL + "    \"pong\""
write_source(mod_path, mod_src)

val main_src = "use sml_sys_mod_single." + "{" + "ping" + "}" + NL + NL + "print ping()"
write_source(main_path, main_src)

val (stdout, stderr, code) = process_run(find_simple_binary(), ["run", main_path])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("pong")

file_delete(mod_path)
file_delete(main_path)
```

</details>

#### use module imports multiple functions

1. write source
2. write source
   - Expected: code equals `0`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "/tmp/sml_sys_mod_multi.spl"
val main_path = "/tmp/sml_sys_main_multi.spl"

val mod_src = "fn foo() -> text:" + NL + "    \"foo\"" + NL + NL + "fn bar() -> text:" + NL + "    \"bar\""
write_source(mod_path, mod_src)

val main_src = "use sml_sys_mod_multi." + "{" + "foo, bar" + "}" + NL + NL + "print foo()" + NL + "print bar()"
write_source(main_path, main_src)

val (stdout, stderr, code) = process_run(find_simple_binary(), ["run", main_path])
expect(code).to_equal(0)
expect(stdout).to_contain("foo")
expect(stdout).to_contain("bar")

file_delete(mod_path)
file_delete(main_path)
```

</details>

#### imported function can call local function in its module

1. write source
2. write source
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `49`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "/tmp/sml_sys_mod_local.spl"
val main_path = "/tmp/sml_sys_main_local.spl"

val mod_src = "fn helper() -> i64:" + NL + "    7" + NL + NL + "fn compute() -> i64:" + NL + "    helper() * helper()"
write_source(mod_path, mod_src)

val main_src = "use sml_sys_mod_local." + "{" + "compute" + "}" + NL + NL + "val result = compute()" + NL + interp_print("result")
write_source(main_path, main_src)

val (stdout, stderr, code) = process_run(find_simple_binary(), ["run", main_path])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("49")

file_delete(mod_path)
file_delete(main_path)
```

</details>

### Module System - Function Calls

#### module function with multiple arguments

1. write source
2. write source
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `7`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "/tmp/sml_sys_mod_args.spl"
val main_path = "/tmp/sml_sys_main_args.spl"

val mod_src = "fn max3(a: i64, b: i64, c: i64) -> i64:" + NL + "    var m = a" + NL + "    if b > m:" + NL + "        m = b" + NL + "    if c > m:" + NL + "        m = c" + NL + "    m"
write_source(mod_path, mod_src)

val main_src = "use sml_sys_mod_args." + "{" + "max3" + "}" + NL + NL + "val result = max3(3, 7, 2)" + NL + interp_print("result")
write_source(main_path, main_src)

val (stdout, stderr, code) = process_run(find_simple_binary(), ["run", main_path])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("7")

file_delete(mod_path)
file_delete(main_path)
```

</details>

#### module from one file imports another module

1. write source
2. write source
3. write source
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `25`
4. file delete
5. file delete
6. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lib_path = "/tmp/sml_sys_lib.spl"
val app_path = "/tmp/sml_sys_app.spl"
val main_path = "/tmp/sml_sys_chain_main.spl"

val lib_src = "fn square(n: i64) -> i64:" + NL + "    n * n"
write_source(lib_path, lib_src)

val app_src = "use sml_sys_lib." + "{" + "square" + "}" + NL + NL + "fn sum_squares(a: i64, b: i64) -> i64:" + NL + "    square(a) + square(b)"
write_source(app_path, app_src)

val main_src = "use sml_sys_app." + "{" + "sum_squares" + "}" + NL + NL + "val result = sum_squares(3, 4)" + NL + interp_print("result")
write_source(main_path, main_src)

val (stdout, stderr, code) = process_run(find_simple_binary(), ["run", main_path])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("25")

file_delete(lib_path)
file_delete(app_path)
file_delete(main_path)
```

</details>

### Module System - std Module Access

#### std.text NL is accessible when imported

1. write source
   - Expected: code equals `0`
2. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val main_path = "/tmp/sml_sys_std_text_main.spl"
val main_src = "use std.text." + "{" + "NL" + "}" + NL + NL + "val msg = \"line1\" + NL + \"line2\"" + NL + "print msg"
write_source(main_path, main_src)

val (stdout, stderr, code) = process_run(find_simple_binary(), ["run", main_path])
expect(code).to_equal(0)
expect(stdout).to_contain("line1")
expect(stdout).to_contain("line2")

file_delete(main_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/module_import/module_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Module System - Import Syntax
- Module System - Function Calls
- Module System - std Module Access

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
