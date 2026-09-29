# A declared `text?` local loses its `?` and `.expect()` is refused as `str.expect` (2026-09-13)

Status: OPEN. Pre-existing; found while fixing
`stage2_sanity_link_fails_with_nil_error_payload_2026-09-13.md`.

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
