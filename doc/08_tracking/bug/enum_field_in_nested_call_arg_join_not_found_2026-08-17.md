# `method 'join' not found on value of type enum in nested call context`

- **Filed:** 2026-08-17
- **Status:** FIX LANDED (pending redeploy) — root-caused and fixed 2026-08-17
  in `src/compiler_rust/compiler/src/interpreter_call/core/class_instantiation.rs`
  (`instantiate_class`); the deployed `bin/simple` seed predates the fix, so the
  spec keeps its temporary-local workaround until the next seed redeploy.
- **Severity:** medium — blocks a natural, short expression form; forces a
  temporary local at every call site.

## Symptom

Constructing a struct that has an **enum-typed field** *directly inside another
call's argument list* fails semantic analysis with a message that mentions a
method (`join`) the source never calls:

```
semantic: method 'join' not found on value of type enum in nested call context
```

## Minimal shape

```simple
# FAILS
ctx.record_instantiation(InstantiationEntry(
    template_name: "Vec",
    ...
    status: InstantiationStatus.Compiled
))

# WORKS — bind first
val status: InstantiationStatus = InstantiationStatus.Compiled
val entry = InstantiationEntry(..., status: status)
ctx.record_instantiation(entry)
```

## Where observed

`test/01_unit/compiler/linker/linker_context_spec.spl`, example
`"records instantiation metadata entries"`.
Types: `InstantiationEntry` / `InstantiationStatus` from
`src/compiler/40.mono/monomorphize/note_sdn.spl:15,101`.
Consumer: `LinkerCompilationContext.record_instantiation`,
`src/compiler/70.backend/linker/linker_context.spl:62`.

## Root cause (found 2026-08-17)

Not nested-call-specific and not an enum-typing path. `instantiate_class`
(seed interpreter, `interpreter_call/core/class_instantiation.rs`) auto-routes
`Type(args)` to a `new` method whenever `args.len()` matches `new`'s param
count and every named arg matches a `new` param NAME — param TYPES are never
checked. `InstantiationEntry` has an impl-static
`new(template_name, type_args: [ConcreteType], ...)` whose 7 param names
coincide with the struct's 7 field names, so the fully-named struct literal
`InstantiationEntry(..., type_args: "i64", status: ...Compiled)` was silently
dispatched to `new`, which ran `type_args.map(&:to_string).join(",")` on
misbound args — the spurious `join` error escapes from inside `new`. The
"nested call context" framing was incidental (that's just the dispatcher that
surfaced the error first); a statement-position literal takes a different route
in the spec's import setup, which is why the bind-first workaround passed.

Minimal repro (fails identically in statement position, no nesting needed):
a struct with an impl-static `new` whose param names mirror the fields but one
param type differs (`tags: [text]` vs field `tags: text`), constructed with a
fully-named literal.

## Fix

`class_instantiation.rs`: a fully-named literal whose arg names all match the
type's OWN fields, on a value-type struct OR when the name-coincident `new` is
a `static fn` (an associated constructor, invoked as `Type.new(...)`), now
builds the struct directly instead of auto-calling `new`. Python-style
non-static `fn new` and `@inject` constructors still auto-route. The
`is_static` half is required because the spec-module registration path
registers structs with `is_value_type=false` (the same defect reproduced
inside `describe`/`it` blocks even in statement position).

Repro + generalization specs (per testing.md two-spec rule):
`test/01_unit/compiler/interpreter/struct_literal_not_routed_to_static_new_spec.spl`
— 5/5 GREEN on a seed built from this tree (isolated CARGO_TARGET_DIR, not
deployed); 3/5 on the currently deployed pre-fix seed (the two literal-routing
examples RED, as expected until redeploy). The exact failing form from this
doc prints `1` (entry recorded) on the fixed seed, and A/B against a control
build of the same tree without the fix shows no spec deltas
(transform_adapters_spec 67/67, artifact_receipt_spec 7/7 on both;
linker_context_spec is zero-examples RED on BOTH fresh builds due to the
unrelated `spl_fonts`/extern-wiring regression tracked in
`interpreter_extern_registration_wiring_clobbered_2026-08-17.md`).

## Unblock condition

Remove the temporary-local workaround from
`test/01_unit/compiler/linker/linker_context_spec.spl` (and its
`test/unit/...` mirror) and the spec must stay green.
