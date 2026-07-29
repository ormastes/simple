# Bug: module-array push+reassign is stale after the SAME function also defines a nested closure over it (interpreter)

- **Date:** 2026-07-29
- **Status:** open (worked around in `test/01_unit/lib/std/concurrency/promise_spec.spl`;
  root cause is in the interpreter, not fixable from pure Simple source beyond the
  workaround)
- **Severity:** HIGH — silently wrong results (stale read after mutation), no error,
  on the default test engine
- **Found by:** lane PRM1 (mission-critical robustness campaign — `Promise.new`
  static constructor)

## Symptom

`test/01_unit/lib/std/concurrency/promise_spec.spl` defines a local, self-contained
`class Promise<T>` (not importing `src/lib/nogc_async_mut/async/promise.spl`, which is
a different type with a different API). The class had no `static fn new`, causing 7 of
19 examples to fail with `semantic: unknown static method new on class Promise` —
that half is a genuinely missing constructor (not the erased-receiver static-method
landmine at `driver_core_types.spl:150`; this receiver type is concrete and other
static constructors like `CancellationToken.new()` resolve fine).

Adding a JS-style executor constructor exposed a **second**, independent interpreter
defect. First attempt (see git history of this spec):

```
var _promise_new_state: [PromiseState] = []

class Promise<T>:
    state: PromiseState
    callbacks: List

    static fn new(executor) -> Promise<T>:
        val idx = _promise_new_state.len()
        _promise_new_state = _promise_new_state.push(PromiseState.Pending)  # (A)

        fn resolve(v):                                                      # (B)
            if _promise_new_state[idx].is_pending():
                _promise_new_state[idx] = PromiseState.Resolved(v)

        fn reject(e):
            if _promise_new_state[idx].is_pending():
                _promise_new_state[idx] = PromiseState.Rejected(e)

        executor(resolve, reject)
        Promise { state: _promise_new_state[idx], callbacks: [] }           # (C)
```

Resolved the "unknown static method" error, but the constructor test then failed a
**second** way: `p.is_resolved()` returned `false` even though the executor called
`resolve(100)` inside `Promise.new(\resolve, reject: resolve(100))`. Read (C) always
returned `Pending`, never the value written from inside the nested closure (B).

## Root cause (minimally repro'd, isolated from this file's names)

The break is: **when a module `var` array is push-and-reassigned (`arr =
arr.push(x)`) inside the SAME function body that also defines a nested named `fn`
referencing that array, the enclosing function's own subsequent reads of the array
go stale (miss writes the nested closure made) — even though the nested closure's
OWN read/write of the array, right after it writes, is internally consistent.**
Moving the push+reassign into a separate top-level free function (called from the
outer function, no nested closure in that separate function) makes both sides see
the same live array.

Minimal repro (`/tmp/.../mini_repro3.spl` and `mini_repro4.spl` during this lane,
arbitrary names):

```
var _reg: [i64] = []

fn make(executor):
    val idx = _reg.len()
    _reg = _reg.push(0)      # push+reassign INLINE in the same fn as the closure

    fn setv(v):
        _reg[idx] = v

    executor(setv)
    print(_reg[idx])         # prints 0 -- STALE (should be 42)
    print(_reg)               # prints [0]  -- the push+reassign target itself lost the write

fn main():
    make(\setv: setv(42))
```

Inside `setv`, printing `_reg[idx]` immediately after the write correctly shows `42`
(confirmed in `mini_repro3.spl`), but the outer `make`'s subsequent read of the exact
same expression `_reg[idx]` shows `0`, and printing the whole array shows `[0]` (not
`[42]`) — i.e. `make`'s view of `_reg` after the local `_reg = _reg.push(0)`
reassignment appears to become a *distinct copy* from the module-level array that the
nested `setv` closure resolves and mutates, even though before the closure runs, both
apparently point at "the same" freshly-pushed array.

**Fix that works** (`mini_repro4.spl`): hoist the push+reassign into a separate
top-level `fn` with no nested closure of its own:

```
var _reg: [i64] = []

fn push_get_idx() -> i64:
    val idx = _reg.len()
    _reg = _reg.push(0)
    idx

fn make(executor):
    val idx = push_get_idx()   # <-- indirection through a free fn, no local push+reassign

    fn setv(v):
        _reg[idx] = v

    executor(setv)
    print(_reg[idx])            # prints 42 -- correct
    print(_reg)                  # prints [42] -- correct
```

This is the workaround shipped in `promise_spec.spl`'s
`_promise_new_push_pending()` helper.

## Relationship to `interpreter_module_array_stale_read_via_free_fn_helper_2026-07-29.md`

Same general family (module-array staleness around free-function indirection and
nested-closure environments in the tree-walk interpreter), but **opposite polarity**:
that doc found free-function indirection *causes* staleness (inline reads inside the
owning method are correct; going through a helper `fn` is stale). This repro found
the free-function indirection *fixes* staleness (inline push+reassign in the same
scope as a nested closure is stale; hoisting to a helper `fn` is correct). Both are
real, reproduced independently, and point at the same underlying suspect: the
interpreter's environment/frame handling around `var` rebinding (`arr = arr.push(x)`)
interacting differently with call-frame scoping depending on whether the write and a
nested closure share one frame or are split across two. Not root-caused further by
this lane; filed for the interpreter/compiler team per the same reasoning as the
referenced doc (not expressible/fixable from pure-Simple stdlib source beyond
case-by-case workarounds).

## Suggested next step

Bisect whether the divergence is specifically about a `var` reassignment
(`_reg = _reg.push(x)`, which is sugar for rebind-whole-array) sharing a call frame
with a nested `fn` definition that references the same module var, versus doing the
same rebind with no nested closure present in that frame (expected: no staleness) or
a nested closure present but the rebind hoisted one frame away (this repro: no
staleness). If confirmed, the interpreter's environment capture for nested `fn`s may
be snapshotting the module binding's *storage location* at closure-creation time
rather than resolving it dynamically on each access when the enclosing frame later
rebinds it.
