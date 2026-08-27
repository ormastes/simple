# Native Backend E2e System Specification

> Tests covering Native Backend E2E - Control Flow, Native Backend E2E - Structs and Pattern Matching, Native Backend E2E - Error Handling.

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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compiles while loop with counter
   - Expected: comp_code equals `0`
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles while loop with counter")
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

- compiles while loop with break
   - Expected: comp_code equals `0`
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles while loop with break")
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

- compiles nested if-else chain
   - Expected: comp_code equals `0`
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles nested if-else chain")
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

- compiles struct construction and field access
   - Expected: comp_code equals `0`
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles struct construction and field access")
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

- compiles match expressions
   - Expected: comp_code equals `0`
   - Expected: code equals `0`
   - Expected: stdout.trim() equals `two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compiles match expressions")
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

- reports non-zero exit code for missing source file


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports non-zero exit code for missing source file")
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

- reports non-zero exit code for syntax error in source


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports non-zero exit code for syntax error in source")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Native Backend E2E - Control Flow, Native Backend E2E - Structs and Pattern Matching, Native Backend E2E - Error Handling.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e0226246a22e556dad0272cc189bf0c344bf99c14b49649598f943567e43a6a2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e0226246a22e556dad0272cc189bf0c344bf99c14b49649598f943567e43a6a2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e0226246a22e556dad0272cc189bf0c344bf99c14b49649598f943567e43a6a2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/compiler/native_backend_e2e_system_spec.spl
mirror: doc/06_spec/03_system/compiler/native_backend_e2e_system_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/native_backend_e2e_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/native_backend_e2e_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/native_backend_e2e_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/compiler/native_backend_e2e_system_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles while loop with counter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/native_backend_e2e_system_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles while loop with break' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/native_backend_e2e_system_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles nested if-else chain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
