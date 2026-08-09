# `native-build` MIR lowering fails to resolve `FileHandle` instance methods for `rt_io_file_roundtrip` — new blocker after the `File` symbol ordering/collision fix

## Summary

Follow-up to
`doc/08_tracking/bug/native_build_mir_lowering_undefined_file_symbol_2026-08-08.md`,
which is now RESOLVED (the `undefined variable: File` failure was a
Dict-method-name collision in `lower_method_call`'s dict-receiver probe, not a
cross-module lowering-order bug; fixed in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`).

With that fix landed, the `rt_io_file_roundtrip` native-build repro (same
recipe as the resolved doc, ~18 minutes to a definitive result) gets past
every `File`-class call (`File.delete`, `File.exists`) and now fails later,
on `FileHandle` INSTANCE methods instead:

```
[ERROR] MIR error: MIR lowering error: undefined variable: h
[ERROR] MIR error: MIR lowering error: unresolved method call: write_text
[ERROR] MIR error: MIR lowering error: unresolved method call: close
[ERROR] MIR error: MIR lowering error: undefined variable: h
[ERROR] MIR error: MIR lowering error: unresolved method call: read_text
[ERROR] MIR error: MIR lowering error: undefined variable: c
[ERROR] MIR error: MIR lowering error: unresolved method call: size
[ERROR] MIR error: MIR lowering error: undefined variable: n
[ERROR] MIR error: MIR lowering error: unresolved method call: close
[ERROR] MIR error: MIR lowering error: unresolved method call: merge
...
error: MIR lowering error: undefined variable: h
```

`h`/`c`/`n` are the `match ...: case Ok(h): h` / `case Ok(c): c` /
`case Ok(n): n` bindings in `main.spl` (lines 18, 43, 48) — real local
variables, not classes, so this is a different mechanism than the resolved
`File`/`Dict`-collision bug. The `write_text`/`close`/`read_text`/`size`/
`read_all`/`write_all`/`merge` unresolved-method-call errors are `FileHandle`
INSTANCE methods called on those locals (plus internal cross-method calls
inside `file.spl`'s own 31 lowered functions).

## Likely mechanism (not yet root-caused this session — filed for follow-up)

`lower_method_call`'s `Unresolved` arm (`method_calls_literals.spl`, doc
comment "Bug #138/#156 keystone") already documents this exact class of gap:
native-build never runs the HIR type-inference pass (30.types), so
`receiver.type_` is nil for ordinary locals, and instance-method dispatch
falls back to `struct_value_syms` (populated at construction/copy sites) to
recover the receiver's struct NAME. A `FileHandle` obtained via `case Ok(h):
h` from `FileHandle.open(...)`'s `Result` payload is exactly the kind of
non-construction-site binding that fallback may not cover — `struct_value_syms`
is set at explicit `StructName(...)` construction and at a few known
propagation sites (global reads, method-call results via
`remember_call_hir_return`/`remember_method_return_provenance`), but a value
extracted through a `match`/`case Ok(h)` binding on a `Result<FileHandle, E>`
is a different provenance path and may not be threaded through.

## Why this matters for the `rt_io_file_*` AOT stub question

Still genuinely UNDETERMINED under true AOT/LLVM codegen — the build now
fails one layer later (at `FileHandle` instance methods) instead of at
`File` static methods, but still never reaches codegen for this fixture.

## Next steps

1. Root-cause why `struct_value_syms` (or the `Ok(h)` match-binding's HIR
   provenance) doesn't carry the `FileHandle` struct name through to the
   instance-method dispatch site. Compare against a fixture that calls an
   instance method directly on a `FileHandle.open(...).unwrap()` chain vs.
   the `match`-destructured `Ok(h)` binding form used here, to see if the
   binding form specifically is the gap.
2. Once fixed, re-run the exact repro (or the fence script's
   `RUN_AOT_LEG=1` leg) to get the actual stub/no-stub verdict for
   `rt_io_file_*`.

## Evidence

Two independent full closure-source (`src/compiler`+`src/app`+`src/lib`)
native-build runs of `rt_io_file_roundtrip/main.spl`, both ~18 minutes,
both stopping at this exact error set after the `File`-symbol fix landed.
Not attached (large trace logs); reproducible via the recipe in the
resolved doc above.
