# Direct Bootstrap System Tests

**Feature ID:** #BOOTSTRAP-002 | **Category:** Runtime | **Status:** Active

_Source: `test/feature/compiler/bootstrap_spec.spl`_

---

## Overview

Tests core language features required for bootstrap without depending on the SSpec framework.
Validates basic execution, arithmetic, string interpolation, function definition and invocation,
for-loop iteration, array creation and traversal, class instantiation with methods, pattern
matching, optional types, and dictionary access. Each test prints a pass/fail indicator directly
to stdout.

## Syntax

```simple
fn double(x: i64) -> i64:
    x * 2
val result = double(21)

val dict = {"one": 1, "two": 2, "three": 3}
val value = dict["two"]
```

---


