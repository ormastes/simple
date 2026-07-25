# Backend System Specification

> 1. print "

<!-- sdn-diagram:id=backend_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend System Specification

## Scenarios

### Backend System - Compilation Outcomes

#### native binary produces correct exit code zero

1. print "
2. file write
   - Expected: comp_code equals `0`
   - Expected: file_exists(out_path) is true
   - Expected: code equals `0`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if gcc_available() == false:
    print "  (skipped: gcc not found)"
    return

val src_path = "/tmp/sml_bsys_exit.spl"
val out_path = "/tmp/sml_bsys_exit_out"
file_write(src_path, "fn main():" + NL + "    print \"ok\"")

val (comp_out, comp_err, comp_code) = compile_native(src_path, out_path)
expect(comp_code).to_equal(0)
expect(file_exists(out_path)).to_equal(true)

val (stdout, stderr, code) = process_run(out_path, [])
expect(code).to_equal(0)

file_delete(src_path)
file_delete(out_path)
```

</details>

#### compiled binary output matches expected string exactly

1. print "
2. file write
   - Expected: comp_code equals `0`
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `exact output test`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if gcc_available() == false:
    print "  (skipped: gcc not found)"
    return

val src_path = "/tmp/sml_bsys_exact.spl"
val out_path = "/tmp/sml_bsys_exact_out"
file_write(src_path, "fn main():" + NL + "    print \"exact output test\"")

val (comp_out, comp_err, comp_code) = compile_native(src_path, out_path)
expect(comp_code).to_equal(0)

val (stdout, stderr, code) = process_run(out_path, [])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("exact output test")

file_delete(src_path)
file_delete(out_path)
```

</details>

#### compiled binary handles integer arithmetic

1. print "
2. write source
   - Expected: comp_code equals `0`
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `42`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if gcc_available() == false:
    print "  (skipped: gcc not found)"
    return

val src_path = "/tmp/sml_bsys_arith.spl"
val out_path = "/tmp/sml_bsys_arith_out"
val src = "fn main():" + NL + "    val x = 6" + NL + "    val y = 7" + NL + "    val result = x * y" + NL + "    " + interp_print("result")
write_source(src_path, src)

val (comp_out, comp_err, comp_code) = compile_native(src_path, out_path)
expect(comp_code).to_equal(0)

val (stdout, stderr, code) = process_run(out_path, [])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("42")

file_delete(src_path)
file_delete(out_path)
```

</details>

#### compiled binary handles string concatenation

1. print "
2. file write
   - Expected: comp_code equals `0`
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `hello world`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if gcc_available() == false:
    print "  (skipped: gcc not found)"
    return

val src_path = "/tmp/sml_bsys_strcat.spl"
val out_path = "/tmp/sml_bsys_strcat_out"
file_write(src_path, "fn main():" + NL + "    print \"hello\" + \" \" + \"world\"")

val (comp_out, comp_err, comp_code) = compile_native(src_path, out_path)
expect(comp_code).to_equal(0)

val (stdout, stderr, code) = process_run(out_path, [])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("hello world")

file_delete(src_path)
file_delete(out_path)
```

</details>

### Backend System - Multi-Line Programs

#### compiles program with multiple print statements

1. print "
2. write source
   - Expected: comp_code equals `0`
   - Expected: code equals `0`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if gcc_available() == false:
    print "  (skipped: gcc not found)"
    return

val src_path = "/tmp/sml_bsys_multi.spl"
val out_path = "/tmp/sml_bsys_multi_out"
val src = "fn main():" + NL + "    print \"line one\"" + NL + "    print \"line two\"" + NL + "    print \"line three\""
write_source(src_path, src)

val (comp_out, comp_err, comp_code) = compile_native(src_path, out_path)
expect(comp_code).to_equal(0)

val (stdout, stderr, code) = process_run(out_path, [])
expect(code).to_equal(0)
expect(stdout).to_contain("line one")
expect(stdout).to_contain("line two")
expect(stdout).to_contain("line three")

file_delete(src_path)
file_delete(out_path)
```

</details>

#### compiles multi-step arithmetic

1. print "
2. write source
   - Expected: comp_code equals `0`
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `55`
3. file delete
4. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if gcc_available() == false:
    print "  (skipped: gcc not found)"
    return

val src_path = "/tmp/sml_bsys_steps.spl"
val out_path = "/tmp/sml_bsys_steps_out"
val src = "fn main():" + NL + "    val a = 10" + NL + "    val b = 20" + NL + "    val c = 25" + NL + "    val total = a + b + c" + NL + "    " + interp_print("total")
write_source(src_path, src)

val (comp_out, comp_err, comp_code) = compile_native(src_path, out_path)
expect(comp_code).to_equal(0)

val (stdout, stderr, code) = process_run(out_path, [])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("55")

file_delete(src_path)
file_delete(out_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/backend_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Backend System - Compilation Outcomes
- Backend System - Multi-Line Programs

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
