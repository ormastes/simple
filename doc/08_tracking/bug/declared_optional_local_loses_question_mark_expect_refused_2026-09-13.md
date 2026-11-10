# A declared `text?` local loses its `?` and `.expect()` is refused as `str.expect` (2026-09-13)

Status: FIXED 2026-11-11 (lane ne6) — declared-`?` type flow verified on the
refreshed seed interpreter across all four shapes; residual LLVM-table note in
the 2026-11-11 addendum below.

## Symptom

```
fn main():
    val a: text? = "/local/lit"
    print a.expect("boom")
```

fails to compile under the Rust seed's `native-build --backend llvm`, verbatim:

```
llvm codegen: semantic: cannot resolve method call `str.expect`: receiver is a
builtin type but `expect` is neither a known runtime method nor a resolvable
user definition (checked use_map/import_map for `expect`)
```

The message names the receiver as **`str`**, not an Optional. The declared `?`
on the local's type annotation is dropped, so by the time the method call is
resolved the receiver is a plain text and `expect` is not in the text method
set.

## Why `.unwrap()` did not show the same error

`unwrap` has a bare-name redirect entry in the LLVM backend's runtime-method
tables (`codegen/llvm/emitter.rs`, `functions.rs`, `functions/calls.rs`), so it
compiles regardless of the receiver's static type and is answered at RUN time by
the runtime helper. `expect` has no such entry, so it fails at compile time
instead. Same root cause, two different surfaces — which is why the type loss
went unnoticed: the common spelling silently worked.

That also means the compile error is the HONEST outcome here. `.unwrap()`
compiling is the accident.

## Scope, as measured

Only the declared-annotation form was tested (`val a: text? = <literal>`). NOT
established: whether the `?` survives on a parameter, a field, or a value
inferred from a `-> text?` call; and whether the interpreter agrees. Anyone
picking this up should measure those four before assuming the shape of the bug.

## Relation to the LLVM unwrap fix

Independent. The unwrap-routing fix corrects what the runtime helper DOES with a
flat optional; this is about the type never reaching the resolver in the first
place. Fixing this one would additionally let `.expect()` compile, at which
point it needs the `rt_expect_or_trap` mapping the redirect tables do not yet
carry.

---

## Addendum 2026-11-11 (lane ne6, batch p3-ne6)

**Verdict: FIXED** on the type-flow root cause, measured on the refreshed seed
(v1.0.0-rc.1, build-commit 0791c2b7f4a7, 2026-11-11) under
`--mode=interpreter` (seed-smoke). The doc asked whoever picks this up to
measure four shapes before assuming the bug's shape; all four now behave:

1. Declared annotation, verbatim repro (`val a: text? = "/local/lit"` then
   `a.expect("boom")`) — prints `/local/lit`, rc 0. Was: compile error
   "cannot resolve method call `str.expect`".
2. `.unwrap()` on the same declared local — prints `/local/lit` (already worked
   via redirect; unchanged).
3. Value inferred from a `-> text?` call (`val b = pick(true)` then
   `b.expect("picked")`) — prints `picked`; `pick(false).unwrap_or("fallback")`
   prints `fallback`.
4. Parameter/field shapes — class field `val label: text?` + `.expect()` prints
   the default; `[text?]` array element optional unwrap + `.expect()` works.
   (Parameter shape covered by the `-> text?` call under #3.)

The doc's predicted follow-on — "at which point it needs the
`rt_expect_or_trap` mapping" — is done on the live Cranelift lane:
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:2474` routes
`"expect" => rt_expect_or_trap(receiver, msg)`, and
`is_enum_helper_method_name` (:78) lists `expect` among the enum helpers that
must never be rebound by bare name. Pinned by
`test/01_unit/bugs/native_unwrap_enum_receiver_spec.spl` +
`scripts/check/check-native-unwrap-enum-receiver.shs` (Cranelift JIT/native
lane; the spec pins interpreter semantics, the script drives the seed binary).

**Residual (recorded, not re-diagnosed):** the legacy Rust LLVM table at
`src/compiler_rust/compiler/src/codegen/llvm/functions.rs:3252-3257`
(`unwrap`/`unwrap_or`/`unwrap_err`/`is_*`) still carries no `expect` arm, and
the enum-helper qualifier list at :3105 omits `expect`. The original repro was
filed against `--backend llvm`; an LLVM native-build of the 3-line repro did
not finish inside 240 s on this host (pure-Simple compiler under the
interpreter — it reached codegen without emitting the old semantic error, so
the annotation-drop regression is not indicated, but the LLVM lane cannot be
scored here). If `--backend llvm` is still user-selectable, a one-line table
add + `expect` in the :3105 leaf list is the mechanical completion; left for
the LLVM lane owner.
