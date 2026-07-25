# Core Interpreter Intensive Specification

> <details>

<!-- sdn-diagram:id=core_interpreter_intensive_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=core_interpreter_intensive_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

core_interpreter_intensive_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=core_interpreter_intensive_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Core Interpreter Intensive Specification

## Scenarios

### core.interpreter (integration intensive)

#### evaluates expressions and main

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "    val b = a push
2. "    if b contains
3. "        return b len
   - Expected: val_get_int(r) equals `3`
4. "    if s contains
5. "        return s len
   - Expected: val_get_int(r2) equals `3`
   - Expected: err contains `no method`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. "fn main
2. "    var p = Point
   - Expected: val_get_int(r) equals `5`
   - Expected: err contains `no field`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/core_interpreter_intensive_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- core.interpreter (integration intensive)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
