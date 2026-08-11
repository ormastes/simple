# BUG: two `test/01_unit/std` specs are permanently red — one imports a class that does not exist, one asserts nothing

**Status:** OPEN (architectural — blocked on owner decision, not a lane-fixable defect)
**Re-verified:** 2026-08-10 — `bin/simple test test/01_unit/std/mock_simple_spec.spl`
still fails identically: `semantic: variable \`Mock\` not found`,
`SPEC FILE VERDICT ... executed=1 passed=0 failed=1`. `grep -rnE "(pub )?class
Mock\b" src/lib/` still returns zero hits (only `MockFunction`, `MockRegistry`,
etc. exist) — root cause is unchanged. `standalone_test.spl` still has no
`describe`/`it`/`expect` and is still a zero-assertion script. Neither can be
resolved without an owner choosing feature-vs-delete (see "Why not fixed now"
below); doing either unilaterally would manufacture a false green, which this
repo's mandate explicitly forbids.
**Found:** 2026-08-04
**Severity:** low-medium — two permanently-failing files, and one of them is
counted as a test while containing zero assertions.
**Files:**
- `test/01_unit/std/mock_simple_spec.spl` (+ legacy duplicate `test/unit/std/mock_simple_spec.spl`)
- `test/01_unit/std/standalone_test.spl` (+ legacy duplicate `test/unit/std/standalone_test.spl`)

## Symptom 1 — `mock_simple_spec.spl` imports a nonexistent `Mock`

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test test/01_unit/std/mock_simple_spec.spl
  ✗ imports Mock
    semantic: variable `Mock` not found
Results: 1 total, 0 passed, 1 failed
```

The file, in full:

```
use spec.{describe, it, expect}
use spec.{Mock}

describe "Mock Simple Import":
    it "imports Mock":
        val m = Mock.new("test")
        assert_true(m.name == "test")
```

Actual: `Mock` does not resolve. Expected: it does, or the spec goes away.

### Root cause

There is no class named `Mock` in the library at all:

```
$ grep -rnE "(pub )?class Mock" --include=*.spl src/lib/
src/lib/nogc_sync_mut/src/testing/mock/builder.spl:36:class MockFunction:
src/lib/nogc_sync_mut/src/testing/mock/builder.spl:223:class MockRegistry:
src/lib/nogc_sync_mut/src/testing/mock/builder.spl:262:class MockPolicy:
src/lib/nogc_sync_mut/src/testing/mock/verification.spl:264:class MockSnapshot:
src/lib/nogc_sync_mut/src/testing/mock/verification.spl:285:class MockComposition:
...
```

— `MockFunction`, `MockRegistry`, `MockPolicy`, `MockSnapshot`,
`MockComposition`, but no bare `Mock`. Nor is any `Mock` re-exported from the
spec package: `grep -rn "\bMock\b" src/lib/nogc_sync_mut/spec*` returns nothing,
and `src/lib/nogc_sync_mut/spec/` contains only `condition`, `decorators`,
`engine_probe`, `env_detect`, `evidence_receipt`, `feature_doc`, `mod`.

The file's own header says **"Status: Complete"**, which is false — this API was
never shipped under this name.

## Symptom 2 — `standalone_test.spl` contains no assertions at all

The file, in full:

```
# Local stub for cached
# (import not resolvable in interpreter mode)
fn cached(f):
    f

fn main():
    fn square(x):
        return x * x
    val c = cached(square)
    print "Standalone success!"
```

Actual: `Results: 1 total, 0 passed, 1 failed` — no `describe`, no `it`, no
`expect`, so the runner has nothing to execute.

### Root cause

Two compounding defects:

1. **No examples.** The filename matches `_test.` so the runner indexes it as a
   spec, but it is a script. Its "success" was a `print` — it could not have
   failed even if `cached` were broken.
2. **Shim vacuity.** The comment `# Local stub for cached / (import not
   resolvable in interpreter mode)` is explicit: rather than import the real
   `cached`, it defines a local `fn cached(f): f` — an identity function — and
   then never even calls the result. Whatever `cached` is meant to do, this file
   has never tested it.

## Why not fixed now

Both need an owner decision that a test-repair lane cannot make:

- For `mock_simple_spec.spl`: either a `Mock` facade is genuinely wanted over
  `MockFunction` (then it is a library feature, to be written with real
  assertions), or the spec should be **deleted**. Renaming the import to
  `MockFunction` would produce a green file that tests one constructor and
  nothing the original spec was about — a false green, so it is deliberately
  not done here.
- For `standalone_test.spl`: the real `cached` needs to be located and imported,
  and the file rewritten as an actual spec with an oracle that can fail. If
  `cached` is not reachable from a spec, that unreachability is the bug to fix
  and should be filed on its own. Deleting the file is also acceptable —
  what is not acceptable is leaving a zero-assertion file counted as a test.

Neither may be resolved by `@skip`/`@ignore` or by deleting the assertions.
