# `expr as Trait` on a trait-typed value has no native lowering (2026-10-19)

## Status: FIXED in MIR (2026-10-20) — native green proof waits for the next Stage 2; std.io workaround kept

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

## Correction and fix (2026-10-20)

**Root cause was misdiagnosed above.** `x as T` parses to `ExprKind.Cast` and
reaches MIR as `HirExprKind.Cast`, not `HirExprKind.As` (no HIR lowering site
produces `As`). `lower_cast_or_convert` emitted a raw scalar `Cast` of the
two-word trait object, so the result lost its trait type and the next method
call failed. r16b Stage 2 (`645e62a815d076d7`, `--threads 1`) on
`test/fixtures/native_trait_cast/same_module/main.spl`:

```
MIR lowering error: unresolved method call: close_n at .../cast1/main.spl:27:16
```

**Fix** (`50.mir/_MirLowering/native_trait_conversion.spl`,
`native_trait_dispatch.spl`, `lower_cast_or_convert` in `expr_dispatch.spl`):

- Every trait-object vtable gains a TRAILING slot: a per-concrete-type cast
  thunk `(data, target_trait_id) -> object word | nil word`. It is appended
  after the method slots, so method slots keep `index + 2`.
- The thunk is emitted where a concrete type becomes a trait object
  (`coerce_native_trait_object`), the one site that knows the concrete type.
  It compares the requested trait id (`hm_hash_text(owner)`, same scheme as
  enum runtime ids; a collision among one type's impls is `error_fatal`)
  against every implementation of that concrete type visible to the
  converting module and builds the target trait object around the same data
  pointer.
- `e as T` on a trait-typed `e` calls the source vtable's cast thunk and
  yields `T?` (`nil` when the dynamic type does not implement `T`), so
  `if val c = e as T:` works. On a concrete `e` it converts statically and
  fails the build when the type has no implementation of `T`. A missing or
  non-object-safe target trait is `error_fatal`.

**Known limit:** an implementation declared in a module the CONVERTING module
does not import is not in its cast thunk and answers `nil`. Casting modules
need not import the implementor (fixture `cross_module`).

**Other limits (Opus review, 2026-10-20):**
- On a TRAIT-typed source the result is `T?` while HIR types the `Cast` as
  `T`. Closed 2026-10-20 (follow-up PR): the `T?` form is lowered ONLY as the
  operand of `.?` (`if val c = e as T:` desugars to `c = (e as T).?`); every
  other position (`val c = e as T`, an argument, a method receiver) is the
  compile error `E-MIR-TRAIT-CAST-CONTEXT`. Same-trait `e as T` stays plain
  `T`. Typing it `T?` in HIR remains the general fix.
  Native-vs-interpreter gap: other genuine Optional consumers (`??`, `?.`,
  `match` on Some/nil, `return` from a `-> T?` fn, `val c: T? = e as T`,
  `(e as T) != nil`) are ALSO rejected natively for now -- a native
  limitation, not language semantics; HIR `T?` typing would admit them.
- An implementation rejected by `native_trait_implementation_rejection`
  (e.g. relying on default methods) is skipped by the cast thunk and casts
  to `nil`.
- Each conversion site emits copy/method thunks for every object-safe trait
  of the concrete type (code size / compile time, deduplicated per module).
- Cast-id collisions are refused at the cast site against every visible
  trait layout, and inside the thunk among the concrete type's traits.

**Interpreter note:** the Rust seed's `as Trait` is a no-op, not a checked
downcast (`ReadOnly as Closer` is non-nil and `c.close_n()` returns 3). The
native semantics follow the checked-downcast meaning the original
`buffer.spl` code relied on.

**Evidence:**
- Spec `test/01_unit/compiler/50.mir/trait_to_trait_cast_lowering_spec.spl`:
  red before the fix (2/2 failed, `unresolved method call: close_n`), green
  after (3/3, including one cast-thunk call plus copy/slot calls in `close_via`).
- Native: red on r16b for both fixtures (`same_module` above; `cross_module`, where the casting module imports only the traits, fails identically with `unresolved method call: close_n`). r16b predates the fix, so the native green
  proof (`both 107` / `readonly -1` for both fixtures) needs the next Stage 2.

**buffer.spl workaround kept** until that Stage 2 proves the cast natively.
