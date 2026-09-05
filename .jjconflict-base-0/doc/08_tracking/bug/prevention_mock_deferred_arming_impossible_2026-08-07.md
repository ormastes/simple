# Prevention-mock deferred arming is impossible under this interpreter; `std.spec.*` also can't reach it

**Date:** 2026-08-07
**Area:** `src/lib/nogc_sync_mut/spec.spl` (Unit U2, `sspec_prevention_mock_plan_2026-08-07.md`)
**Status:** OPEN (re-confirmed 2026-08-09) — architectural, not a local bug:
the interpreter's cross-scope class-instance value semantics (Defect 1) and
lack of persistent module-level state across `it` examples (Defect 2) are the
root causes, both out of scope for a local patch in this file. `prevent`/
`prevent_at_most`/`prevent_file`
ship with immediate-check semantics instead of the plan's originally intended
"arm early, auto-check at end of `_execute_it`" design.

## Defect 1 — any storage of a class instance snapshots it by value

The plan's original design: `prevent(mockfn, reason)` called at the *top* of an
`it` body pushes a `ForbiddenCallGuard` into a module-level array; `_execute_it`
walks that array after the block runs and turns any triggered guard into a
failure. This is impossible: the interpreter copies a class instance
(`MockFunction`) by value on **every** storage mechanism tried, and only
continued access through the *original* variable observes later mutations.

Verified three independent ways, with a clean control:

- **Class-field construction** (`ForbiddenCallGuard.new(mockfn, reason)` then
  storing the guard): guard built before `m.record_call(...)`, then
  `check_guards([...])` — reports `msgs.len()=0` instead of `1`.
- **Raw array push** (`probe_mocks.push(m)` then `m.record_call(...)` then
  `probe_mocks[0].call_count()`) — reads `0`.
- **Closure capture** (`fn() -> i64: mockfn.call_count()` pushed into an
  array, mock mutated after capture) — reads `0`.
- **Control (works correctly):** direct var mutation and read
  (`m.record_call(...)`; `m.call_count()` → `1`), and passing the mock by
  function parameter into a helper that mutates it (`mutate_it(m)`; caller's
  `m.call_count()` → `1`). Confirms `MockFunction` is a genuine mutable
  reference type; the defect is specific to cross-scope *storage*, not to
  mutation itself.
- **Isolated control for array storage identity**: mutating *through the
  stored array element itself* (`probe_mocks[0].record_call(...)`; then
  `probe_mocks[0].call_count()`) correctly reads `1` — the stored copy is
  itself a live, mutable object; it is simply a *different* object from the
  variable that was pushed.

Repro file (deleted after use, not landed):
`test/01_unit/lib/std/testing/zz_probe_prevent_defect_spec.spl`, probes 1-6.

## Defect 2 — module-level spec state does not persist across `it` examples

Even setting Defect 1 aside, file-scope prevention (`prevent_file` armed once
at the top of a spec file, auto-checked after every example) requires
module-level state to survive from one `it` example to the next. It does not:

```
var probe_counter = 0
var probe_fm = MockFunction.new("cross-example")

it "example 1": probe_counter = probe_counter + 1; probe_fm.record_call(["a"])
  # -> counter=1 calls=1 (as expected, within the example)
it "example 2": print "counter={probe_counter} calls={probe_fm.call_count()}"
  # -> counter=0 calls=0  (BOTH reset — even a bare i64 counter)
```

This means true directory-wide *and* true file-wide auto-checked prevention
are both unreachable under the current runner, for a reason unrelated to
Defect 1: each example appears to run against fresh module state. This is
consistent with the plan's own (separately filed) finding for directory-wide
scope in `doc/08_tracking/bug/sspec_no_dir_wide_prevention_scope_2026-08-07.md`
— file scope turns out to have the same root cause.

## Defect 3 — `use std.spec.*` does not expose every `pub fn`, including pre-existing ones

Independent of the above: `use std.spec.*` (the wildcard import used by every
other spec file in the repo, per `spec.spl`'s own header docstring) does not
reliably resolve every `pub fn` defined in `src/lib/nogc_sync_mut/spec.spl` —
including a **long-standing, unedited** function, `get_test_count()`, which
has been in the file well before this unit and is still `function not found`
through the wildcard:

| import form | symbol | result |
|---|---|---|
| `use std.nogc_sync_mut.spec.{name}` (fully-qualified, explicit) | any newly-added `pub fn` | **resolves** |
| `use std.nogc_sync_mut.spec.*` (fully-qualified, wildcard) | same symbol | not found |
| `use std.spec.{name}` (alias, explicit) | same symbol | not found |
| `use std.spec.*` (alias, wildcard) | `fail_assertion` (pre-existing, long in use) | resolves |
| `use std.spec.*` (alias, wildcard) | `get_test_count` (pre-existing, **not new**) | **not found** |

This rules out a staleness/caching theory (a fully-qualified *wildcard* import
of a brand-new symbol also fails, and an explicit *fully-qualified* import of
the same symbol succeeds — two independent axes, not one) and rules out a
curated-re-export-list theory (`get_test_count` predates this unit entirely
and is still unreachable). No cache directory, symbol-index file, alias
registry, or running daemon was found to explain it (checked:
`~/.cache/simple`, `.simple/native_cache/incremental_manifest.txt`,
`src/compiler/**/alias_registry.spl`, `pgrep -af test_daemon`). This looks
like a genuine, pre-existing gap in how the wildcard-star import resolves
symbols for the `std.spec` module/alias — separate from and unrelated to Unit
U2's own changes, and out of scope to fix here.

**Consequence for this unit:** `prevent`, `prevent_at_most`, and
`prevent_file` must be imported explicitly and fully-qualified —
`use std.nogc_sync_mut.spec.{prevent, prevent_at_most, prevent_file}` — not
via the conventional `use std.spec.*` that the rest of the test suite relies
on. This is documented at the top of the "Prevention mocks" section in
`spec.spl` and must be called out again wherever U4/U5 document or adopt the
DSL.

## Unblock conditions

- Defect 1/2 (real fix, not scope-around): would need either (a) a
  genuine mutable-reference semantics for class instances stored in
  arrays/closures/class-fields in the interpreter, or (b) per-directory/
  per-file runner state that survives across `it` examples (this may be the
  same underlying gap as the directory-wide runner-discovery limitation in
  `sspec_no_dir_wide_prevention_scope_2026-08-07.md` — worth investigating
  together).
- Defect 3: needs investigation into how `use std.spec.*`/`use <alias>.*`
  wildcard resolution actually enumerates a module's exported symbol set,
  ideally by someone with visibility into the compiler's import-resolution
  pass (`src/compiler/**`), which was not chased further here to stay in
  scope for Unit U2.

## What ships instead (honest scope)

`prevent(mockfn, reason)`, `prevent_at_most(mockfn, n, reason)`, and
`prevent_file(mockfn, reason)` in `src/lib/nogc_sync_mut/spec.spl` check
IMMEDIATELY against `mockfn`'s current state at the point they are called —
they do not arm early and do not defer. Call them **after** the code under
test has run, same as the pre-existing manual idiom
(`check_guards([...])` + `expect`), just as one line instead of three.
`prevent_file` is a documented alias for `prevent` — it does not provide
automatic cross-example checking; callers must invoke it in every example (or
from `before_each`/`after_each`) to approximate file-wide coverage.

## Re-verification (2026-08-09)

`src/lib/nogc_sync_mut/spec.spl` still defines `prevent` (line 615),
`prevent_at_most` (line 622), and `prevent_file` (line 628) with the
immediate-check shape described above — no deferred-arming implementation has
landed, and none of the three unblock conditions (mutable cross-scope
class-instance storage, persistent module-level state across `it` examples,
or wildcard-import symbol resolution) have been addressed. The scope-around
documented here remains correct and current. No code change made: a genuine
fix requires interpreter-level semantic changes (mutable-reference storage
semantics and/or persistent per-file spec state) that are out of scope for a
local patch, exactly as the original report concluded.
