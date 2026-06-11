# Module Loader E2e Specification

> 1. write source

<!-- sdn-diagram:id=module_loader_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_loader_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_loader_e2e_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_loader_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Loader E2e Specification

## Scenarios

### Module Loader E2E - Basic Import

#### loads a module via use and calls its function

1. write source
2. write source
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `hello from module`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "/tmp/sml_e2e_hello_mod.spl"
val main_path = "/tmp/sml_e2e_hello_main.spl"

val mod_src = "fn say_hello():" + NL + "    print \"hello from module\""
write_source(mod_path, mod_src)

val main_src = "use sml_e2e_hello_mod." + "{" + "say_hello" + "}" + NL + NL + "say_hello()"
write_source(main_path, main_src)

val (stdout, stderr, code) = process_run(find_simple_binary(), ["run", main_path])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("hello from module")

file_delete(mod_path)
file_delete(main_path)
```

</details>

#### imports a function that returns a numeric value

1. write source
2. write source
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `42`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "/tmp/sml_e2e_val_mod.spl"
val main_path = "/tmp/sml_e2e_val_main.spl"

val mod_src = "fn get_answer() -> i64:" + NL + "    42"
write_source(mod_path, mod_src)

val main_src = "use sml_e2e_val_mod." + "{" + "get_answer" + "}" + NL + NL + "val result = get_answer()" + NL + interp_print("result")
write_source(main_path, main_src)

val (stdout, stderr, code) = process_run(find_simple_binary(), ["run", main_path])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("42")

file_delete(mod_path)
file_delete(main_path)
```

</details>

#### imports multiple functions from the same module

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
val mod_path = "/tmp/sml_e2e_multi_mod.spl"
val main_path = "/tmp/sml_e2e_multi_main.spl"

val mod_src = "fn add(a: i64, b: i64) -> i64:" + NL + "    a + b" + NL + NL + "fn mul(a: i64, b: i64) -> i64:" + NL + "    a * b"
write_source(mod_path, mod_src)

val main_src = "use sml_e2e_multi_mod." + "{" + "add, mul" + "}" + NL + NL + "val s = add(3, 4)" + NL + "val p = mul(3, 4)" + NL + interp_print("s") + NL + interp_print("p")
write_source(main_path, main_src)

val (stdout, stderr, code) = process_run(find_simple_binary(), ["run", main_path])
expect(code).to_equal(0)
expect(stdout).to_contain("7")
expect(stdout).to_contain("12")

file_delete(mod_path)
file_delete(main_path)
```

</details>

#### module function takes and returns text

1. write source
2. write source
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `Hello, World!`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "/tmp/sml_e2e_text_mod.spl"
val main_path = "/tmp/sml_e2e_text_main.spl"

val mod_src = "fn greet(name: text) -> text:" + NL + "    \"Hello, \" + name + \"!\""
write_source(mod_path, mod_src)

val main_src = "use sml_e2e_text_mod." + "{" + "greet" + "}" + NL + NL + "print greet(\"World\")"
write_source(main_path, main_src)

val (stdout, stderr, code) = process_run(find_simple_binary(), ["run", main_path])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("Hello, World!")

file_delete(mod_path)
file_delete(main_path)
```

</details>

### Module Loader E2E - Transitive Dependencies

#### loads transitive dependencies A uses B uses C

1. write source
2. write source
3. write source
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `20`
4. file delete
5. file delete
6. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base_path = "/tmp/sml_e2e_base.spl"
val mid_path = "/tmp/sml_e2e_mid.spl"
val main_path = "/tmp/sml_e2e_trans_main.spl"

val base_src = "fn double(x: i64) -> i64:" + NL + "    x * 2"
write_source(base_path, base_src)

val mid_src = "use sml_e2e_base." + "{" + "double" + "}" + NL + NL + "fn quad(x: i64) -> i64:" + NL + "    double(double(x))"
write_source(mid_path, mid_src)

val main_src = "use sml_e2e_mid." + "{" + "quad" + "}" + NL + NL + "val result = quad(5)" + NL + interp_print("result")
write_source(main_path, main_src)

val (stdout, stderr, code) = process_run(find_simple_binary(), ["run", main_path])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("20")

file_delete(base_path)
file_delete(mid_path)
file_delete(main_path)
```

</details>

#### double import of same module works (caching)

1. write source
2. write source
3. write source
   - Expected: code equals `0`
4. file delete
5. file delete
6. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "/tmp/sml_e2e_cached_mod.spl"
val helper_path = "/tmp/sml_e2e_cached_helper.spl"
val main_path = "/tmp/sml_e2e_cached_main.spl"

val mod_src = "fn value() -> i64:" + NL + "    100"
write_source(mod_path, mod_src)

val helper_src = "use sml_e2e_cached_mod." + "{" + "value" + "}" + NL + NL + "fn doubled() -> i64:" + NL + "    value() * 2"
write_source(helper_path, helper_src)

val main_src = "use sml_e2e_cached_mod." + "{" + "value" + "}" + NL + "use sml_e2e_cached_helper." + "{" + "doubled" + "}" + NL + NL + "val a = value()" + NL + "val b = doubled()" + NL + interp_print("a") + NL + interp_print("b")
write_source(main_path, main_src)

val (stdout, stderr, code) = process_run(find_simple_binary(), ["run", main_path])
expect(code).to_equal(0)
expect(stdout).to_contain("100")
expect(stdout).to_contain("200")

file_delete(mod_path)
file_delete(helper_path)
file_delete(main_path)
```

</details>

### Module Loader E2E - Arithmetic Modules

#### module with factorial computes correctly

1. write source
2. write source
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `120`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_path = "/tmp/sml_e2e_fact_mod.spl"
val main_path = "/tmp/sml_e2e_fact_main.spl"

val mod_src = "fn factorial(n: i64) -> i64:" + NL + "    if n <= 1:" + NL + "        return 1" + NL + "    return n * factorial(n - 1)"
write_source(mod_path, mod_src)

val main_src = "use sml_e2e_fact_mod." + "{" + "factorial" + "}" + NL + NL + "val result = factorial(5)" + NL + interp_print("result")
write_source(main_path, main_src)

val (stdout, stderr, code) = process_run(find_simple_binary(), ["run", main_path])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("120")

file_delete(mod_path)
file_delete(main_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/module_import/module_loader_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Module Loader E2E - Basic Import
- Module Loader E2E - Transitive Dependencies
- Module Loader E2E - Arithmetic Modules

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
