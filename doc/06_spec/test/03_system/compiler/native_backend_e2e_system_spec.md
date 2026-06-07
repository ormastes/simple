# Native Backend E2e System Specification

> <details>

<!-- sdn-diagram:id=native_backend_e2e_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_backend_e2e_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_backend_e2e_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_backend_e2e_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Backend E2e System Specification

## Scenarios

### Native Backend E2E - Control Flow

<details>
<summary>Advanced: compiles while loop with counter</summary>

#### compiles while loop with counter _(slow)_

1. print "
2. write source
   - Expected: comp_code equals `0`
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `5`
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

val src_path = "/tmp/sml_sys_while.spl"
val out_path = "/tmp/sml_sys_while_out"
val src = "fn main():" + NL + "    var i = 0" + NL + "    while i < 5:" + NL + "        i = i + 1" + NL + "    " + interp_print("i")
write_source(src_path, src)

val (comp_out, comp_err, comp_code) = compile_native(src_path, out_path)
expect(comp_code).to_equal(0)

val (stdout, stderr, code) = process_run(out_path, [])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("5")

file_delete(src_path)
file_delete(out_path)
```

</details>


</details>

<details>
<summary>Advanced: compiles while loop with break</summary>

#### compiles while loop with break _(slow)_

1. print "
2. write source
   - Expected: comp_code equals `0`
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `3`
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

val src_path = "/tmp/sml_sys_break.spl"
val out_path = "/tmp/sml_sys_break_out"
val src = "fn main():" + NL + "    var i = 0" + NL + "    while true:" + NL + "        i = i + 1" + NL + "        if i >= 3:" + NL + "            break" + NL + "    " + interp_print("i")
write_source(src_path, src)

val (comp_out, comp_err, comp_code) = compile_native(src_path, out_path)
expect(comp_code).to_equal(0)

val (stdout, stderr, code) = process_run(out_path, [])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("3")

file_delete(src_path)
file_delete(out_path)
```

</details>


</details>

<details>
<summary>Advanced: compiles nested if-else chain</summary>

#### compiles nested if-else chain _(slow)_

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

val src_path = "/tmp/sml_sys_ifelse.spl"
val out_path = "/tmp/sml_sys_ifelse_out"
val src = "fn classify(x: i64) -> text:" + NL + "    if x < 0:" + NL + "        return \"negative\"" + NL + "    if x == 0:" + NL + "        return \"zero\"" + NL + "    return \"positive\"" + NL + NL + "fn main():" + NL + "    print classify(-1)" + NL + "    print classify(0)" + NL + "    print classify(1)"
write_source(src_path, src)

val (comp_out, comp_err, comp_code) = compile_native(src_path, out_path)
expect(comp_code).to_equal(0)

val (stdout, stderr, code) = process_run(out_path, [])
expect(code).to_equal(0)
expect(stdout).to_contain("negative")
expect(stdout).to_contain("zero")
expect(stdout).to_contain("positive")

file_delete(src_path)
file_delete(out_path)
```

</details>


</details>

### Native Backend E2E - Structs and Pattern Matching

<details>
<summary>Advanced: compiles struct construction and field access</summary>

#### compiles struct construction and field access _(slow)_

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

val src_path = "/tmp/sml_sys_struct.spl"
val out_path = "/tmp/sml_sys_struct_out"
val src = "struct Pair:" + NL + "    left: i64" + NL + "    right: i64" + NL + NL + "fn main():" + NL + "    val pair = Pair(left: 20, right: 22)" + NL + "    print pair.left + pair.right"
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


</details>

<details>
<summary>Advanced: compiles match expressions</summary>

#### compiles match expressions _(slow)_

1. print "
2. write source
   - Expected: comp_code equals `0`
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `two`
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

val src_path = "/tmp/sml_sys_match.spl"
val out_path = "/tmp/sml_sys_match_out"
val src = "fn main():" + NL + "    val value = 2" + NL + "    val label = match value:" + NL + "        0: \"zero\"" + NL + "        1: \"one\"" + NL + "        2: \"two\"" + NL + "        _: \"other\"" + NL + "    print label"
write_source(src_path, src)

val (comp_out, comp_err, comp_code) = compile_native(src_path, out_path)
expect(comp_code).to_equal(0)

val (stdout, stderr, code) = process_run(out_path, [])
expect(code).to_equal(0)
expect(stdout.trim()).to_equal("two")

file_delete(src_path)
file_delete(out_path)
```

</details>


</details>

### Native Backend E2E - Error Handling

<details>
<summary>Advanced: reports non-zero exit code for missing source file</summary>

#### reports non-zero exit code for missing source file _(slow)_

1. print "


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if gcc_available() == false:
    print "  (skipped: gcc not found)"
    return

val src_path = "/tmp/sml_sys_missing_does_not_exist_xyz.spl"
val out_path = "/tmp/sml_sys_missing_out"

val (comp_out, comp_err, comp_code) = compile_native(src_path, out_path)
expect(comp_code).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: reports non-zero exit code for syntax error in source</summary>

#### reports non-zero exit code for syntax error in source _(slow)_

1. print "
2. file write
3. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if gcc_available() == false:
    print "  (skipped: gcc not found)"
    return

val src_path = "/tmp/sml_sys_syntax_err.spl"
val out_path = "/tmp/sml_sys_syntax_err_out"
file_write(src_path, "fn broken(: bad syntax here @@@@")

val (comp_out, comp_err, comp_code) = process_run(find_simple_binary(), ["run", "src/app/compile/native.spl", src_path, out_path])
expect(comp_code).to_be_greater_than(0)

file_delete(src_path)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/native_backend_e2e_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Native Backend E2E - Control Flow
- Native Backend E2E - Structs and Pattern Matching
- Native Backend E2E - Error Handling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 7 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
