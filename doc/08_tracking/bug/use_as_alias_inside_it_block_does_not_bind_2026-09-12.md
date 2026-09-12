# `use ... as alias` inside an `it` block does not bind the alias (the stack overflow it replaced is gone)

- Status: OPEN (2026-09-12)
- Area: compiler / module resolution, spec runner
- Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`, sha256 prefix `3d120a6f`

## What changed

Six TODO markers across the spec tree say:

```
# TODO: use statements inside it blocks cause stack overflow
# This is a known limitation - use must be at module level
```

(`test/03_system/interpreter/interpreter_bugs_spec.spl:83,129`,
`test/system/interpreter/interpreter_bugs_spec.spl:83,129`,
`test/03_system/compiler/parser_improvements_spec.spl:219`,
`test/system/compiler/parser_improvements_spec.spl:209`.)

**The stack overflow is gone.** Measured 2026-09-12:

```
use std.spec.*
describe "use inside it":
    it "can import a module inside an it block":
        use std.common.text.{trim}
        expect(trim("  x  ")).to_equal("x")
```
-> `outcome=OK declared>=1 executed=1 passed=1 failed=0`

A brace-form import of a class works the same way
(`use std.spec.condition.{SkipCondition}` then constructing it: OK 1/1).

## The residual defect

The **alias** form still does not bind, and fails with a plain
name-resolution error rather than an overflow:

```
use std.spec.step
use std.spec.*

describe "alias use inside it":
    it "imports with an alias inside an it block":
        use std.spec as sp2
        sp2.expect(1 == 1)

    it "imports a submodule with an alias inside an it block":
        use std.spec.condition as cond2
        val c = cond2.SkipCondition(platforms: [], runtimes: [], profiles: [], architectures: [])
        expect(c.platforms.len()).to_equal(0)
```
->
```
semantic: variable `sp2` not found
semantic: variable `cond2` not found
outcome=ERROR declared>=2 executed=2 passed=0 failed=2
```

So `use X.{A, B}` binds inside a block and `use X as Y` does not. The same
`use X as Y` at module level works.

## Impact

Small but misleading: the six markers above document a limitation with the
wrong cause, which is why they survived long after the overflow was fixed. The
markers were removed in the todo-fix lane and replaced with in-block brace
imports that actually exercise the capability; this record carries the part
that is still broken.

## Not fixed here

Binding an `as` alias in block scope is a resolver change in the compiler, not
a spec edit.
