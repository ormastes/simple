# Native codegen: calling a closure VALUE (not a name) SIGSEGVs/aborts

Date: 2026-09-07
Found while: clearing the macOS Stage-4 final-link undefined-symbol list
(`_UiAccessPersistence.insert_event_fn`, `_UiAccessPersistence.persist_snapshot_fn`).

## Symptom

Any call through a closure-typed value crashes under the LLVM/native backend,
even in the simplest possible shape. The interpreter runs the same code
correctly.

```
fn main():
    val f: fn(i64) -> i64 = \x: x * 2
    val r = f(5)
    println("{r}")
```

- Interpreter (`build/seedfix/bootstrap/simple run`): prints `10`.
- Native (`native-build --backend llvm ...`): links fine, then the produced
  binary exits with signal (observed exit 133, i.e. SIGTRAP/abort).

A closure stored in a class FIELD and called through a local variable crashes
the same way, but with SIGSEGV (exit 139) instead:

```
class Persistence:
    insert_event_fn: fn(i64) -> i64

fn make_persistence() -> Persistence:
    Persistence(insert_event_fn: \x: x * 2)

fn main():
    val p = make_persistence()
    val insert_event = p.insert_event_fn
    val r = insert_event(5)   # or: val r = p.insert_event_fn(5)
    println("{r}")
```

Both the field-read-then-call form and the direct `p.insert_event_fn(5)` form
crash identically natively.

## Relationship to the link-fix in this change

`src/lib/nogc_sync_mut/ui/session.spl`'s `_persist_latest_access_event` and
`_sync_access_store_snapshot` originally called
`self.access_persistence.insert_event_fn(latest)` / `...persist_snapshot_fn(snapshot)`
directly. Under the LLVM backend that dotted call was mis-resolved as a CLASS
METHOD lookup on `UiAccessPersistence` (which has no such method --
`insert_event_fn`/`persist_snapshot_fn` are closure-typed FIELDS), leaving
`_UiAccessPersistence.insert_event_fn` / `_UiAccessPersistence.persist_snapshot_fn`
undefined at the final link.

The fix in this change (read the field into a local, then call the local with
no dot) makes the call target unambiguous to the mangler/codegen and clears
the undefined-symbol link failure. It does NOT fix the SEGV documented here --
that is a separate, deeper native-codegen defect in how ANY closure value
(field or plain variable) is invoked. `UISession.access_persistence` is
normally `nil` unless a caller explicitly calls `attach_access_persistence`,
so this code path is not exercised by default and the Stage-4 macOS build
links and (for the default nil-persistence case) runs; only a caller that
actually attaches a `UiAccessPersistence` and drives an access event through
native code would hit the SEGV.

## Scope note

Not investigated further here (out of scope for the link-fix task): whether
this affects EVERY closure call under native codegen (a fundamental ABI gap)
or only specific shapes (e.g. closures with non-trivial capture, or captured
vs. non-capturing lambdas). The two reproductions above are both
non-capturing single-argument lambdas and both crash, which suggests the gap
is broad rather than narrow, but this was not exhaustively characterized.

## Repro fixtures

Both reproductions above were run via the fast single-file native-build probe
(`native-build --backend llvm --runtime-bundle core-c-bootstrap ...`) against
`build/seedfix/bootstrap/simple` (this session's Stage-4 seed) and compared
against `build/seedfix/bootstrap/simple run` (interpreter) for the same
source. No fixture files were left in the tree; recreate from the snippets
above to reproduce.
