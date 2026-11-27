# JIT: member access through a whole-module import is unresolved (fn) or garbage (const)

- **Filed:** 2026-11-13
- **Severity:** P3 (the const form is a silent wrong value; see below)
- **Status:** FIXED (work/jit-use-alias-20261113; spec 4/10 -> 10/10)
- **Lane:** seed (`src/compiler_rust`), `simple run` Cranelift JIT, flattened unit
- **Spec:** `test/01_unit/compiler/jit_module_namespace_import_spec.spl`
- **Fixture:** `test/fixtures/jit_use_alias/src/`

## Symptom

Triage reported this as "`use X as Y` fails under the JIT with `GlobalLoad:
unresolved identifier`". The repro shows the trigger is a **whole-module
import**, with or without an alias. Item aliases work.

Seed built from `origin/release/1.0.0` `c63348a42db`, `SIMPLE_EXECUTION_MODE=jit`:

| Form | Fixture | Result on base |
|---|---|---|
| `use alib.core.{alias_add as plus_two}` | `item_alias_fn` | 42, stays on JIT |
| `use alib.core.{ALIAS_BASE as BASE_ALIAS}` | `item_alias_const` | 42, stays on JIT |
| `use alib.core.alias_add as plus_two` | `single_alias_fn` | 42, stays on JIT |
| `use alib.core.ALIAS_BASE as BASE_ALIAS` | `single_alias_const` | 42, stays on JIT |
| `use alib.core as ac` + `ac.alias_add(40)` | `module_alias_fn` | 42 only after demotion: `GlobalLoad: unresolved identifier 'ac'` |
| `use alib.core as ac` + `ac.ALIAS_BASE + 2` | `module_alias_const` | **garbage** (e.g. `390867236518`), no demotion |
| `use alib.core` + `core.alias_add(40)` | `module_plain_fn` | 42 only after demotion: `... 'core'` |
| `use alib.core` + `core.ALIAS_BASE + 2` | `module_plain_const` | **garbage** (e.g. `680580396710`), no demotion |
| namespace import inside a non-entry module | `nested_namespace` | 42 only after demotion: `... 'c2'` |

The fn forms exit 0 with the right answer, because the default JIT lane falls
back to the interpreter (`[engine-demotion] reason=jit-compile-error`). That
fallback is a silent 100-1000x slowdown for the whole program.

The const forms are worse. They never demote. `val x = ac.ALIAS_BASE` holds
an `<enum@0x...>` object, so `x + 2` prints a different large number on every
run. The interpreter lane prints 42 for every form.

## Root cause

`pipeline::module_loader` flattens a whole-module import of a module file
(`single_import_targets_module_file`), so `alias_add` and `ALIAS_BASE` are in
the JIT unit. But `append_flattened_import_binding_markers` records nothing
for a whole-module import (`ImportTarget::Single`/`Aliased` with
`target_is_symbol == false`), because it binds no symbol. HIR lowering
therefore had no way to know that `ac` (or `core`) names
`alib/core.spl`:

- `ac.alias_add(...)`: `lower_method_call` consults `qualified_import_functions`,
  which only the native-project lane populates. It then lowers the receiver to
  `Global("ac")`. Codegen refuses that with `GlobalLoad: unresolved identifier`.
- `ac.ALIAS_BASE`: `lower_field_access` lowers the receiver to a value and
  emits a dynamic field read off it, which yields an unrelated object.

## Fix

The flattener emits a separate marker (`__simple_flatten_module_namespace__=`,
importer / local name / source owner) for every whole-module import. It does
not reuse the import-binding prefix, because whole-module imports bind no
symbol and that prefix has several consumers. HIR lowering decodes the marker
per importer. `ns.f(...)` resolves through `flatten_reexport_definer` and
`flatten_emitted_symbol`. `ns.CONST` resolves through the per-owner global
census and `flattened_global_symbol`. Both paths are owner-exact. A local
variable, or a real declaration named like the namespace, still wins. A
member the namespace's module does not declare keeps the old path.

The namespace marker is also hoisted with the import-binding markers when
`compile -o *.smf` wraps a script entry (no `fn main`) in a synthesized main
(`native_project::is_import_binding_marker`). On base, compiling a script
that uses `ac.alias_add(ac.ALIAS_BASE)` failed with `GlobalLoad: unresolved
identifier 'ac'`. On head it compiles.

## Still open (not caused by this fix)

- On this host, running any compiled `.smf` crashes on base and on head
  alike (SIGBUS/SIGILL/SIGSEGV, including `print("hi")`), so the compiled
  script could not be executed.
- `simple run` of a script entry with no `fn main` never uses the JIT
  (`jit-bail:no-main-fn`).
- Namespace names are shadowed only by functions and globals, not by
  struct, class or enum names. Two namespace imports with the same local name
  in one importer resolve last-wins. Both are rare; the review rated them P3.
