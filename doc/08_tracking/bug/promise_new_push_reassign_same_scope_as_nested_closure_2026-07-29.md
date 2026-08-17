# Bug: module-array push+reassign is stale after the SAME function also defines a nested closure over it (interpreter)

- **Date:** 2026-07-29
- **Status:** open — STILL LIVE, re-verified by content 2026-08-17 (see
  "Re-verification" below). Worked around in
  `test/01_unit/lib/std/concurrency/promise_spec.spl`. **BLOCKED — OUT OF SCOPE
  for stdlib lanes:** root cause is in the Rust-seed interpreter's global/closure
  environment sync, not in `src/lib/nogc_async_mut/async/promise.spl` (that file
  is innocent; the failing class `Promise` is defined locally inside the spec).
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

## Re-verification 2026-08-17 (still live) + root-cause location

Binary: `bin/release/x86_64-unknown-linux-gnu/simple` (Rust bootstrap seed).
Engine is the tree-walk interpreter — the JIT explicitly declines the module
(`function 'main' creates a lambda/closure; the JIT closure ABI does not
tag-box lambda arguments or results ... deferring to interpreter`), so this is
an interpreter-only defect and cannot be attributed to codegen.

The doc's minimal repro was re-run verbatim under `nice -n 19 timeout 400
bin/simple run` (exit 0) and still shows the stale read:

```
0        # print(_reg[idx]) in make()  -- STALE, expected 42
[0]      # print(_reg)                 -- STALE, expected [42]
```

Unchanged from the 2026-07-29 report — no regression, no fix in the interim.

**Root cause location (do not edit from a stdlib lane).** The interpreter
publishes/refreshes module globals across call frames at explicit sync points
rather than sharing one live cell:

- `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:47`
  `captured_env_with_live_globals(func, captured_env)` — builds a closure's
  environment by SNAPSHOTTING the current global values at call time.
- `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:123`
  `publish_live_bound_globals(env)` — writes a frame's globals back out; it is
  invoked at the call boundaries (lines 172, 825-826, 890-891, 1214-1215).
- `src/compiler_rust/compiler/src/interpreter/block_exec.rs:65-108` and
  `node_exec.rs:659-690` — the `globals.contains_key(...) / globals.insert(...)`
  write-back and `env.refresh_globals(...)` paths.

That snapshot/publish design is exactly consistent with the observed polarity:
a `var` rebind (`_reg = _reg.push(0)`) in the enclosing frame replaces the
frame's LOCAL copy of the global, while the nested `fn` was given (or later
publishes into) a different copy, so the two frames diverge. Hoisting the
rebind into its own free function makes the publish/refresh boundary fall
between the rebind and the closure creation, which is why the documented
workaround works.

This also explains the "opposite polarity" puzzle with
`interpreter_module_array_stale_read_via_free_fn_helper_2026-07-29.md`: both
are the same snapshot-vs-live-cell bug, and which side goes stale is decided
only by where the publish/refresh boundary happens to land relative to the
rebind. They should be fixed together, by making module `var` bindings a shared
mutable cell rather than a per-frame copy that is synced at boundaries.

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

## 2026-08-17 (lane w04) — STILL LIVE, and the trigger is NARROWER than documented

Reproduced at spec level, verbatim:

```
Results: 19 total, 18 passed, 1 failed
```
(`test/01_unit/lib/std/concurrency/promise_spec.spl`, run with
`--no-session-daemon`; the failing example is
`✗ executor receives both callbacks` / `expected subject to be truthy, got false`.)

**The title of this doc is wrong.** Neither `push`+reassign nor an executor
parameter is required. Isolated on `bin/simple run`:

| shape | result |
|---|---|
| module array, push+reassign, nested `fn`, called via executor param | `outer_read=0 module_read=0` — LOST |
| module array, **in-place** `.push`, nested `fn`, via executor param | `inplace_outer=0 inplace_module=0` — LOST |
| module array, push+reassign, **no** nested fn (write inline) | `no_closure_outer=42 no_closure_module=42` — OK |
| module array, nested `fn` called **directly** (no executor param) | `direct_nested_fn=0` — LOST |
| module **scalar** `var`, nested `fn` called directly | `scalar_module_var=42` — OK |

Minimal trigger, with everything else stripped out:

```
var _reg: [i64] = []

fn direct() -> i64:
    _reg = _reg.push(0)
    fn setv(v):
        _reg[0] = v      # write from inside a nested fn
    setv(42)
    _reg[0]              # reads 0
```

So it is **not** about push semantics, reassignment, or higher-order calls. It
is: *a nested named `fn` writing a module-level **container** element by index
loses the write entirely* — invisible both to the enclosing function afterwards
and to module scope after the call returns. The identical nested `fn` writing a
module-level **scalar** var works. That container-vs-scalar split is the
signature to look for in the interpreter's closure/global environment sync.

Root cause remains in the Rust seed interpreter; out of scope for stdlib lanes.
`src/lib/nogc_async_mut/async/promise.spl` remains innocent.
