# core_interpreter_intensive_spec

> Purpose: This spec proves core.interpreter (integration intensive).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# core_interpreter_intensive_spec

Purpose: This spec proves core.interpreter (integration intensive).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/integration/compiler/core_interpreter_intensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves core.interpreter (integration intensive).
Audience: Maintainers of the Simple integration suite reviewing this behavior.

## Scenarios

### core.interpreter (integration intensive)

#### evaluates expressions and main

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- evaluates expressions and main
   - Expected: val_get_int(v) equals `7`
   - Expected: val_get_int(r) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-COREINTERPRETERINTENSIVE-001
step("evaluates expressions and main")
if _can_run:
    val v = run_expr_ok("1 + 2 * 3")
    expect(val_get_int(v)).to_equal(7)

    val prog = "fn main():\n" +
        "    return 2 + 3\n"
    val r = run_ok(prog)
    expect(val_get_int(r)).to_equal(5)
else:
    print "SKIP: requires compiled mode"
```

</details>

<details>
<summary>Advanced: handles control flow and loops</summary>

#### handles control flow and loops

- handles control flow and loops
- handles control flow and loops
   - Expected: val_get_int(r) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles control flow and loops")
step("handles control flow and loops")
if _can_run:
    val prog = "fn main():\n" +
        "    var sum = 0\n" +
        "    for i in [1, 2, 3]:\n" +
        "        if i == 2:\n" +
        "            continue\n" +
        "        sum = sum + i\n" +
        "    var n = 0\n" +
        "    while n < 2:\n" +
        "        sum = sum + n\n" +
        "        n = n + 1\n" +
        "    return sum\n"
    val r = run_ok(prog)
    expect(val_get_int(r)).to_equal(5)
else:
    print "SKIP: requires compiled mode"
```

</details>


</details>

#### handles match and arrays

- handles match and arrays
- handles match and arrays
   - Expected: val_get_int(r) equals `20`
   - Expected: val_get_int(r2) equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles match and arrays")
step("handles match and arrays")
if _can_run:
    val prog = "fn main():\n" +
        "    val x = 2\n" +
        "    match x:\n" +
        "        case 1:\n" +
        "            return 10\n" +
        "        case 2:\n" +
        "            return 20\n" +
        "    return 0\n"
    val r = run_ok(prog)
    expect(val_get_int(r)).to_equal(20)

    val prog2 = "fn main():\n" +
        "    var a = [10, 20, 30]\n" +
        "    return a[1]\n"
    val r2 = run_ok(prog2)
    expect(val_get_int(r2)).to_equal(20)
else:
    print "SKIP: requires compiled mode"
```

</details>

#### handles array/text methods and errors

- handles array/text methods and errors
- handles array/text methods and errors
   - Expected: val_get_int(r) equals `3`
   - Expected: val_get_int(r2) equals `3`
   - Expected: err contains `no method`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles array/text methods and errors")
step("handles array/text methods and errors")
if _can_run:
    val prog = "fn main():\n" +
        "    var a = [1, 2]\n" +
        "    val b = a.push(3)\n" +
        "    if b.contains(2):\n" +
        "        return b.len()\n" +
        "    return 0\n"
    val r = run_ok(prog)
    expect(val_get_int(r)).to_equal(3)

    val prog2 = "fn main():\n" +
        "    val s = \"abc\"\n" +
        "    if s.contains(\"b\"):\n" +
        "        return s.len()\n" +
        "    return 0\n"
    val r2 = run_ok(prog2)
    expect(val_get_int(r2)).to_equal(3)

    val err = run_err("fn main():\n    var a = [1]\n    val x = a.foo()\n    return x\n")
    expect(err.contains("no method")).to_equal(true)
else:
    print "SKIP: requires compiled mode"
```

</details>

#### handles struct fields and assignment

- handles struct fields and assignment
- handles struct fields and assignment
   - Expected: val_get_int(r) equals `5`
   - Expected: err contains `no field`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("handles struct fields and assignment")
step("handles struct fields and assignment")
if _can_run:
    val prog = "struct Point:\n" +
        "    x: i64\n" +
        "    y: i64\n" +
        "fn main():\n" +
        "    var p = Point(1, 2)\n" +
        "    p.x = 5\n" +
        "    return p.x\n"
    val r = run_ok(prog)
    expect(val_get_int(r)).to_equal(5)

    val err = run_err("struct Point:\n    x: i64\nfn main():\n    val p = Point(1)\n    return p.z\n")
    expect(err.contains("no field")).to_equal(true)
else:
    print "SKIP: requires compiled mode"
```

</details>

#### reports common runtime errors

- reports common runtime errors
- reports common runtime errors
   - Expected: err1 contains `undefined variable`
   - Expected: err2 contains `array index out of bounds`
   - Expected: err3 contains `string index out of bounds`
   - Expected: err4 contains `cannot index`
   - Expected: err5 contains `invalid assignment`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports common runtime errors")
step("reports common runtime errors")
if _can_run:
    val err1 = run_err("fn main():\n    return unknown\n")
    expect(err1.contains("undefined variable")).to_equal(true)

    val err2 = run_err("fn main():\n    var a = [1]\n    val x = a[2]\n    return x\n")
    expect(err2.contains("array index out of bounds")).to_equal(true)

    val err3 = run_err("fn main():\n    val s = \"hi\"\n    val x = s[2]\n    return x\n")
    expect(err3.contains("string index out of bounds")).to_equal(true)

    val err4 = run_err("fn main():\n    val x = 1\n    val y = x[0]\n    return y\n")
    expect(err4.contains("cannot index")).to_equal(true)

    val err5 = run_err("fn main():\n    1 = 2\n")
    expect(err5.contains("invalid assignment")).to_equal(true)
else:
    print "SKIP: requires compiled mode"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-COREINTERPRETERINTENSIVE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1e5dd5b325f710be714cab6d86efe015bf1b9b25d8d86ab9f6f04140720095e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e5dd5b325f710be714cab6d86efe015bf1b9b25d8d86ab9f6f04140720095e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e5dd5b325f710be714cab6d86efe015bf1b9b25d8d86ab9f6f04140720095e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/compiler/core_interpreter_intensive_spec.spl
mirror: doc/06_spec/integration/compiler/core_interpreter_intensive_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/compiler/core_interpreter_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/compiler/core_interpreter_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/compiler/core_interpreter_intensive_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/compiler/core_interpreter_intensive_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates expressions and main' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/core_interpreter_intensive_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles control flow and loops' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/compiler/core_interpreter_intensive_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles match and arrays' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
