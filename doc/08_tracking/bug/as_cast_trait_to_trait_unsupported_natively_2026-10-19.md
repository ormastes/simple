# `expr as Trait` on a trait-typed value has no native lowering (2026-10-19)

## Status: OPEN (compiler gap) — std.io call sites restructured around it

## Symptom

r13 Stage 2 (`e6cb4bfd5533a790`, `--threads 1`) could not build the std.io
closure: the four `close()` / `is_open()` bodies in
`src/lib/nogc_async_mut/io/buffer.spl` did

```simple
if val close_inner = self.inner as AsyncClose:
    close_inner.close()
else:
    Future.from_value(Ok(()))
```

where `inner: AsyncRead` (reader) / `inner: AsyncWrite` (writer). The
interpreter treats the `as` as a checked downcast that yields `nil` when the
dynamic object does not implement `AsyncClose`; the self-hosted compiler does
not.

## Root cause (compiler)

- HIR keeps the declared trait on the result of `self.inner as AsyncClose`;
  nothing records a runtime type test.
- MIR has no trait-to-trait dispatch: `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
  lowers every `HirExprKind.As` through
  `unsupported_expr_kind("E-MIR-EXPR-As", "as-cast expression (`expr as Type`)")`
  (line ~6271 at `ab32f432a85`). A trait object carries a vtable for the
  declared trait only, so even a supported `As` would have no second vtable to
  dispatch `close()` against.

Implementing it means: a runtime "implements trait T" test on the object's
type identity plus a vtable lookup for T (or fat pointers carrying a type id),
and `if val x = e as T` lowering to that test. That is a cross-layer change
(HIR type of `as`, MIR op, runtime), not a local fix.

## Decision

Source change in `buffer.spl` (small, no behaviour change for existing
callers) and this record for the compiler gap:

- `AsyncBufferedReader` / `AsyncBufferedWriter` gain `closer: AsyncClose?`.
- `new` / `with_capacity` set `closer: nil` -> `close()` returns `Ok(())` and
  `is_open()` returns `true`, exactly the old else-branches. (No `src/`
  caller constructs these wrappers; the only caller is
  `test/01_unit/lib/nogc_async_mut/io/async_buffer_spec.spl` with an
  AsyncRead-only source, 14/14 green after the change.)
- `new_closing(inner, closer)` forwards `close()` / `is_open()` to the
  source's AsyncClose view (e.g. `AsyncTcpStream`, which implements both).
  Under the interpreter this was previously implicit for `new(tcp_stream)`;
  it is now opt-in, which is the one semantic difference and is intentional:
  the implicit form cannot be compiled natively.

Spec: `test/01_unit/lib/nogc_async_mut/io/async_buffer_closer_spec.spl`.

## Other occurrences

`grep -rn "\bas Async[A-Za-z]*\b" src/lib` — none remain. Any future
`value as Trait` where `value`'s declared type is itself a trait will hit
`E-MIR-EXPR-As` natively; prefer an explicit optional field or a separate
parameter typed as the target trait.
