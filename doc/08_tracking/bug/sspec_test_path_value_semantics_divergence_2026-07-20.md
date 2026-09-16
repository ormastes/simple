# SSpec `test` evaluator diverges from `run` on `.?` operator and class-in-array aliasing

**Status:** Open  **Found:** 2026-07-20 (whole-suite triage cluster, test/03_system/)

This is a **new facet** of the known landmine "`bin/simple test` (SSpec) uses a
DIFFERENT evaluator than `bin/simple run`" (previously documented for static
method / free-symbol resolution in
`generic_class_static_method_unresolved_under_test_2026-07-20.md` and
`enum_impl_static_fn_method_call_path_skips_impl_methods_2026-07-20.md`). This
doc covers a different symptom family: correct **value semantics** under
`run`, wrong under `test`. Do not conflate the mechanism — file separately
from the static-method family per the existing landmine note's guidance.

## Symptom 1 — `.?` (presence/truthiness) operator gives the wrong boolean under `test`

**Affected spec:** `test/03_system/interpreter/interpreter_system_spec.spl`
  - `it "workflow 2 - error handling"` (line 40) — `verify(error.? == true)`
  - `it "error 5 - missing key"` (line 258) — `verify(dict.get("b").? == false)`
  - `it "integration 5 - error propagation"` (line 312) — `verify(error.?)`

All three assign/produce a value via a `var` initialized to `nil`, later
possibly reassigned, or via `dict.get()` on a missing key, then check `.?` on
it. All three fail under `bin/simple test`; the equivalent logic passes under
`bin/simple run`.

Minimal repro (var reassigned nil -> string):

```simple
use std.spec.describe
use std.spec.it
use std.spec.expect

describe "optquestion repro":
    it "binds nil-then-string correctly":
        var error = nil
        val invalid_input = ""
        if invalid_input.len() == 0:
            error = "Empty input"
        expect(error.? == true).to_equal(true)
```

- `bin/simple run` (printing `error.?` and `error != nil` directly): both
  print `true` (correct).
- `bin/simple test`: `✗ binds payload... expected false to equal true` — i.e.
  `error.?` evaluates to `false` under `test` despite `error` holding the
  non-nil string `"Empty input"`.

Minimal repro (`dict.get()` on a missing key):

```simple
use std.spec.describe
use std.spec.it
use std.spec.expect

describe "dict get repro":
    it "missing key .? is false":
        val dict = {"a": 1}
        val r = dict.get("b")
        expect(r.?).to_equal(false)
```

- `bin/simple test`: `✗ missing key .? is false ... expected nil to equal
  false` — i.e. `r.?` evaluates to `nil` (not a boolean at all) under `test`.

**Do not migrate `.?` to `!= nil` as a workaround in these specs.** Checked
this explicitly: (a) `dict.get("b") != nil` under `test` still fails
(`expected nil to not equal nil` — `r != nil` itself evaluates to `nil`
instead of a boolean here, a second distinct symptom), so the migration does
not even fully green the file; and (b) the same spec file has a passing
example (line 194, `"plain empty values remain present without an explicit
existence check"`) that specifically asserts `.?` is a **truthiness** check,
not a nil check (`""` and `[]` are "present" under `.?`) — so `.? -> != nil`
is not semantically equivalent in this codebase and would not be a
value-preserving edit here.

## Symptom 2 — class-in-array element mutation not visible to caller under `test`

**Affected spec:** `test/03_system/interpreter/interp_value_semantics_b35_spec.spl`
  - `describe "Task 112 - class-in-array reference semantics"`,
    `it "class-in-array: mutating a locally-read element leaks to the caller
    through the array slot"` (line 167)

```simple
class SemArrCellB35:
    v: i32

impl SemArrCellB35:
    me set_v(x: i32):
        self.v = x

fn array_class_mutate_b35(arr: [SemArrCellB35]):
    var elem = arr[0]
    elem.set_v(777)
```

```simple
var arr = [SemArrCellB35(v: 42)]
array_class_mutate_b35(arr)
expect(arr[0].v).to_equal(777)
```

Classes are reference types in this language (see the file's own earlier
class-mutation examples, which pass): reading `arr[0]` into a local `elem`
and mutating through it must be visible via the original array slot, since
both alias the same instance.

- `bin/simple run` (same logic via a `main()` + `print`): prints `777`
  (correct).
- `bin/simple test`: `✗ ... expected 42 to equal 777` — the array slot is
  NOT updated; `test`'s evaluator appears to copy the class instance out of
  the array on index-read instead of preserving the reference alias.

## Root-cause hypothesis

Both symptoms point at the `test`-path evaluator handling variable/value
binding and copy-vs-alias semantics differently from the `run`-path
evaluator — consistent with the already-documented "different evaluator"
architecture landmine, but manifesting here as wrong **value semantics**
(copy where alias expected, wrong truthiness result) rather than a resolution
error. This suggests the `test` evaluator's expression/variable-binding layer
independently re-implements read/copy behavior instead of sharing the `run`
path's environment code, and that reimplementation has at least two separate
defects (`.?` truthiness table, and array-index-read aliasing).

## Impact

All 4 affected examples are in regression-guard specs
(`interpreter_system_spec.spl`, `interp_value_semantics_b35_spec.spl`,
per their `describe`/file naming) — i.e. these assert previously-working
behavior and are currently red under `bin/simple test`, the project's default
test-running path.
