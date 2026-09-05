# `describe` as the trailing expression of `fn main() -> ()` leaks a non-zero exit code

Status: OPEN (workaround applied in 6 caret ink specs)
Found: 2026-08-30, via `bin/simple test test/01_unit/app/llm_caret` (8/900 failures)

## Symptom

A spec file whose `describe` runs inside `fn main() -> ()` prints every example
as passing, prints `outcome=OK ... failed=0`, and then **exits 1**. The test
runner reads the non-zero status and synthesizes one phantom failed example, so
the file reports `declared>=N executed=N passed=N-1 failed=1`.

## Minimal reproduction (7 lines)

```
use std.spec.*
fn main() -> ():
    describe "x":
        it "y":
            expect(1).to_equal(1)
```

```
$ bin/simple run /tmp/t.spl
  ✓ y
1 example, 0 failures
SPEC FILE VERDICT: /tmp/t.spl outcome=OK declared>=0 executed=1 passed=1 failed=0 skipped=0 dropped=0
$ echo $?
1
```

## Bisected

| form | exit |
|---|---|
| `describe` at module top level, no `main` | 0 |
| `fn main() -> ()` ending in `print(...)` | 0 |
| `fn main() -> ()` ending in a call to a unit fn that ends in an assignment | 0 |
| `fn main() -> ()` ending in a call taking a closure param | 0 |
| **`fn main() -> ()` ending in `describe(...)`** | **1** |
| same, with an explicit trailing `return ()` | 0 |

Both the block form (`describe "x":`) and the closure form
(`describe("x", fn() -> ():`) reproduce, so this is not a syntax issue.

## Why it matters

`main` is *declared* `-> ()`. A unit-returning function must not be able to put
a value into the process exit status. The status and the verdict line disagree,
which is the same fail-open family as
`test_runner_exits_zero_on_failed_spec_2026-08-21.md` — in the opposite
direction: there a real failure exited 0, here a clean run exits 1. A gate that
trusts the exit code is wrong in both.

## Not yet located

`bdd_failure_exit_code` / `SpecOutcome::exit_code` in
`src/compiler_rust/driver/src/cli/basic.rs:61-350` correctly pass a
`module_exit_code` of 0 through when `failed == 0`, so the 1 is already present
in `module_exit_code` — i.e. it comes from evaluating `main`, not from the BDD
tally. The exact site that turns `main`'s trailing-expression value into the
process status has not been found.

## Workaround in tree

An explicit `return ()` as the last statement of `main`, applied to the six
files under `test/01_unit/app/llm_caret/claude_full/ink/` that hit this, each
marked with a `ponytail:` comment pointing here. Remove the workaround and this
record together when the exit-code path is fixed.
