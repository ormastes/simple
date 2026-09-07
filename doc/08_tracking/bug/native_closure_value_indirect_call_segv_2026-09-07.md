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

## RESOLVED 2026-09-07 — root cause and fix

Confirmed via `SIMPLE_DUMP_IR=1 SIMPLE_DUMP_IR_FILTER=main` (LLVM IR dump env
vars already wired in `functions.rs::compile_function`). Two independent
defects, both in the LLVM/native pipeline, both required to reproduce and fix
in order:

**Defect 1 — the LLVM backend never outlined lambda bodies into standalone
functions.** `codegen::shared::expand_with_outlined` (used by the
Cranelift/JIT `compile_all_functions` path) splits a lambda's body block out
of its parent `MirFunction` into its own top-level function. The LLVM
backend's `NativeBackend::compile` (`codegen/llvm/backend_core.rs`) iterated
`module.functions` directly and never called it. The dumped IR for
reproducer A showed the lambda body surviving only as `bb1: ; No
predecessors!` still inside `@spl_main`, with no `@main_outlined_1` function
anywhere in the module. `compile_closure_create`
(`codegen/llvm/functions/objects.rs`) does
`module.get_function(func_name).unwrap_or_else(|| i8_ptr_type.const_null())`
— missing the function, it silently stored a NULL function pointer into the
closure's fn-ptr slot. The indirect call then loaded and called that null
pointer.
  - Fix: `LlvmBackend::compile` now calls `expand_with_outlined(module)` and
    rebinds `module` to a clone with the expanded function list, before any
    other use of `module.functions`
    (`codegen/llvm/backend_core.rs`, in `compile`).

**Defect 2 (uncovered only after fixing #1) — the AOT name mangler never
rewrote `ClosureCreate::func_name`.** `pipeline/native_project/mangle.rs`'s
`mangle_mir` renames every local function with a body (`main` → `spl_main`
for the entry module, others → `{prefix}__{name}`) in Phase 1, and rewrites
`Call`/`InterpCall`/`MethodCallStatic` targets in Phase 3 — but had no arm
for `MirInst::ClosureCreate`. `ClosureCreate::func_name` is baked at
MIR-lowering time as `"{parent_name}_outlined_{block_id}"` using the
PARENT's PRE-mangling name, while `expand_with_outlined` (which runs later,
per-backend, off the POST-mangling MIR) names the actual outlined function
after the parent's NEW (mangled) name. So even with Defect 1 fixed, the
outlined function was genuinely defined (e.g. `@spl_main_outlined_1`), but
the closure's `func_name` field still said the stale `main_outlined_1`
(dumped IR: `declare weak i64 @spl_main_outlined_1(i64, i64)` alongside a
`ClosureCreate` whose recorded name, per the MIR dump, remained
`main_outlined_1`) — a second, independent miss on the same
`module.get_function` lookup, same NULL-function-pointer consequence.
  - Fix: `mangle_mir` now precomputes an old-prefix → new-prefix rename
    table from `local_mangled` (only for names that actually change) before
    Phase 1 mutates `func.name`, and Phase 3 gained a `ClosureCreate` arm
    that rewrites `func_name` through that table
    (`pipeline/native_project/mangle.rs`).

This is NOT narrow to `main`: any local function whose name is mangled (i.e.
every local function with a body compiled through this AOT pipeline) had the
same closure-outlining name mismatch, so this second defect explains the
broad "affects every closure call under native codegen" scope suspected but
not confirmed in the original write-up above.

### Verified before/after (aarch64-apple-darwin, LLVM backend, single-file probe)

| Repro | Before | After | Interpreter |
|---|---|---|---|
| A (plain local closure) | exit 133 (SIGTRAP) | prints `10`, exit 0 | prints `10` |
| B (closure read from a class field) | exit 139 (SIGSEGV) | prints `10`, exit 0 | prints `10` |

`sh scripts/check/check-c-runtime-compiles-push.shs` — `PASS — 129 file(s)
compiled, 0 errors (6 skipped for unavailable external dependencies)`.
f64 regression check (the `9c67bd56fa4` fix in this same backend) re-verified
unaffected: `val a: f64 = 1.5; val b: f64 = 2.5; println("{a + b}")` still
prints `4.0` natively.

Additional probes (capturing closures — the two original repros are both
non-capturing) verified against the interpreter, all matching:

| Probe | Native | Interpreter |
|---|---|---|
| one capture: `val k = 3; val f = \x: x * k; f(5)` | `15`, rc=0 | `15` |
| two params/two captures: `val a=3; val b=4; val f = \x,y: x*a+y*b; f(5,6)` | `39`, rc=0 | `39` |
| string capture: `val s = "ab"; val f = \x: "{s}{x}"; f(1)` | `ab1`, rc=0 | `ab1` |

Full-CLI Stage-4 relink and `simple test` acceptance status: see the commit
that lands this fix and, if present, a follow-up note below.
