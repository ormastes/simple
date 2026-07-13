# Result unwrap loses receiver type during native method resolution

## Symptom

An unannotated local produced by `Result<T, E>.unwrap()` loses `T` before native
method resolution. If two types define the same method, codegen rejects the call
as ambiguous even though the `Result` payload type is concrete.

The strict Stage-4 build reproduced this in `aot_compile_to_bytes`:

```simple
val module = compiled.unwrap()
module.emit_object(tmp_path)
```

`compiled` is `Result<CompiledModule, CodegenError>`, but resolution considered
both `CompiledModule.emit_object` and `CraneliftCodegenState.emit_object`. Raw and
mangled index aliases inflated the diagnostic from two semantic methods to four
names.

## Bounded workaround

The receiver uses the existing typed-local pattern:

```simple
val module: CompiledModule = compiled.unwrap()
```

This is not a method-name exception. The next strict build compiled the body and
reached the linker.

## Required compiler fix

Preserve generic payload `T` through `unwrap()` into unannotated local type
inference, and deduplicate raw/mangled aliases by function identity in ambiguity
diagnostics. A regression must define two types with the same method and prove
that `Result<A, E>.unwrap().method()` selects `A` without an annotation while an
actually unknown receiver still fails closed.

Tracked by TODO 558.
