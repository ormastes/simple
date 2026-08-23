# Bogus method call on a plain struct is accepted by the frontend and only fails at link

- **Date:** 2026-08-23
- **Status:** OPEN (recorded, not fixed — the resolution fix belongs in its own lane)
- **Class:** unbacked symbol surviving to link — same class as
  `rt_unwrap_or_trap` / NULL-GOT
  (`doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`)
  and `unregistered_extern_silent_nil_2026-08-01.md`.

## Symptom

Calling a method that exists **nowhere** — not on the receiver's type, not in
any `extend` block, not as a free function — on a value whose type is a plain
struct with no methods at all compiles clean. Codegen emits a call to the
mangled symbol `<Type>.<method>`. The defect surfaces only at the final native
link, as an undefined symbol.

## How it was found

Stage 2 of the sanctioned bootstrap compiled 757 object files and died at the
final link with 14 undefined symbols: `OutlineModule.imports_push`,
`.exports_push`, `.functions_push`, `.classes_push`, `.actors_push`,
`.structs_push`, `.enums_push`, `.bitfields_push`, `.traits_push`,
`.impls_push`, `.type_aliases_push`, `.constants_push`, `.static_asserts_push`,
`.errors_push`.

`OutlineModule` is a plain struct declared at
`src/compiler/10.frontend/treesitter_types.spl:20` with array fields and **no
methods**; there is no `extend OutlineModule` anywhere in the tree, and no free
`imports_push` etc. either. The 14 call sites were of the form
`module.imports = module.imports_push(module.imports, i)` in
`src/compiler/10.frontend/treesitter/outline.spl` (lines 845-878) and 14
identical sites in the shadowed facade `src/compiler/10.frontend/treesitter.spl`
(lines 89-122). Both sets are fixed in the same commit as this record; this
record is about the *compiler* defect that let them exist.

It failed CLOSED only because `SIMPLE_NO_STUB_FALLBACK=1` was set for that
bootstrap lane. Without it a stub fallback would have been substituted.

## Minimal reproducer (verified)

`doc/08_tracking/bug/repro/bogus_struct_method_call_2026-08-23.spl`:

```
struct Bag:
    items: [i64]

fn main():
    var b = Bag(items: [])
    b.items = b.items_push(b.items, 1)   # no such method on a plain struct
    print(b.items.len())
```

Observed on the deployed seed, 2026-08-23:

```
$ bin/simple run doc/08_tracking/bug/repro/bogus_struct_method_call_2026-08-23.spl
Runtime error: Function 'Bag.items_push' not found
Runtime error: unresolved symbol -- this is a code-generation dispatch gap, not
a program error. Refusing to substitute a placeholder value ...
rc=70
```

That is the whole defect in one line of evidence: **the failure is a RUNTIME
dispatch error, not a compile-time diagnostic.** The frontend, HIR lowering and
type check all accept `recv.<unknown>(...)` on a struct with no methods and
emit a call to a mangled symbol that no stage ever checks exists. The runtime's
own message even names it correctly — "a code-generation dispatch gap" — but
nothing upstream of codegen refuses it.

## Where the hole is

Located and verified by reading the sources (not inferred):

**The correct gate exists and is not on this lane.**
`src/compiler/35.semantics/resolve_strategies.spl:51-62` is the designed UFCS
`MethodResolver`; it *does* reject this case properly, returning
`MethodResolution.Unresolved` with `"no method '{method}' found for type
'{type_name}'"`. Self-hosted compilation of `src/compiler/**` does not go
through it.

**The permissive lane** is method-call lowering in MIR, whose own comment
concedes the situation —
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1933`: *"the
flat bootstrap HIR has no method resolution"*. Two arms matter:

1. **The arm that produced this bug.** The "name-derived custom-owner
   recovery" at `method_calls_literals.spl:2894-2959` (emit at `:2924-2959`)
   believes it has found a matching method symbol for an unresolved name and
   emits a real `emit_call` against `self.symbol_to_operand(resolved_method_id)`
   — a call to a mangled `<Type>.<method>` symbol with no backing definition.
   That is what becomes an undefined symbol at native link. Note this is *not*
   the `rt_panic` arm below: had the panic arm been reached, the failure would
   have been a runtime trap, not a link error.

2. **The terminal arm, whose diagnostic is dropped.**
   `method_calls_literals.spl:3354` does call
   `self.error("unresolved method call: {method}", nil)` — a genuine
   diagnostic. The file's own comments at `:3355-3375` record that it is
   inert on this lane: *"self.error only COLLECTS -- both the bootstrap lane
   (driver_bootstrap.spl reads ctx.errors, never MirLowering.errors) and the
   native-build worker drop the list"*, and
   `driver_bootstrap.bootstrap_lower_to_mir_context` returns
   `next_ctx.errors.len() == 0` without ever copying the lowering errors in.
   So the build reports success regardless. The accompanying `rt_panic` +
   const-0 placeholder (`:3363-3392`, Task #145) is a deliberate fail-closed
   *runtime* guard; it does not stop the build.

**Which stage should have caught it:** `35.semantics` method resolution should
run on this lane; failing that, `driver_bootstrap` must propagate
`MirLowering.errors` instead of consulting only its own separate `ctx.errors`.
The latter is the cheaper of the two and would have turned this link failure
into a compile diagnostic on the spot.

A related permissive fallback worth reading while fixing is
`lower_unresolved_array_push`, called at `method_calls_literals.spl:2973` and
`:3264`.

## Other sites of the same shape

A tree-wide scan (`scripts/check/check-no-phantom-field-push.shs`, added with
this record) found exactly **28** sites of the precise
`recv.F = recv.F_push(recv.F, v)` shape, all in the two files above; both are
fixed. One near-miss, `self.imported_type_methods_in_progress_push(reentry_key)`
at `src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl:1067`,
was checked and is legitimate — a real `me` method at
`src/compiler/20.hir/hir_lowering/context_helpers.spl:34`.

A broader census of *all* bogus method calls is not achievable by grep: in
Simple, `a.b(...)` is also the spelling of a module-qualified call, so a static
scan cannot distinguish `mock.create_mock(...)` (a namespace call) from a
phantom method without full name resolution. **The link step is the only
complete oracle**, which is exactly why the compiler must do this check itself.

## Fix direction (NOT done here)

Make method resolution fail closed: when a method name resolves to nothing for
the receiver's type, emit a diagnostic naming the type, the method, and the
available methods, instead of mangling and emitting. Expect fallout — the
tree has never been compiled under that rule, so land it behind a ratchet
rather than as a hard flip.

## Pinned by

- `scripts/check/check-no-phantom-field-push.shs` — fail-closed source ratchet
  for the specific shape (fail-closed, `--selftest` fatal with 4 fixtures).
  FAILs on the pre-fix tree naming all 28 sites; PASSes after.
