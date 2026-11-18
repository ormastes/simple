# Stage 3 self-build dies: raw `char*` text reaches strict tagged owners

- **Date:** 2026-11-18
- **Status:** defect 1 fixed in source (MIR-level proof; native proof needs a new Stage 2);
  defect 2 OPEN with a source workaround
- **Lane:** Stage 2 (seed-built, cranelift) -> Stage 3 -> Stage 3 self-build, aarch64 Linux
- **Source pin:** release/1.0.0 `e4e072f8289`

## Symptom

Stage 3 (built by Stage 2) compiling itself, and compiling a two-line hello world:

```
[explicit-source] rejected non-spl path=<...>/src/compiler/20.hir/hir_lowering/types<garbage>
[simple-runtime][error] rejected invalid array handle before dereference ...
PANIC: bounds_check intrinsic index=-1 len=117213        (len=1 for hello world)
```

Stage 2 on identical input prints none of these. The hello-world form reproduces in
seconds, so no self-build is needed to see it.

## Shared root

Natively a `text` value has two representations: a tagged heap handle and a raw
`char*`. A `for x in [text]` binder, an indexed local `[text]` element, some record
fields and literals are raw, and a `text` parameter is whatever its caller passed.
Raw-tolerant code (`==`, print, `.len()`) hides the difference. Two owners do not.

## Defect 1 — strict tagged externs receive a raw `char*` (fixed)

`tagged_text_value_arg_indices` (`src/compiler/50.mir/text_extern_abi.spl`) lists
externs whose `text` operand skips the `rt_interp_cstr` bridge. The call lowerer
(`lower_call_with_value`, `50.mir/_MirLoweringExpr/switch_operators_calls.spl`) then
passed the operand unchanged, whatever it held. `rt_hash_text` decodes with
`rt_core_as_string`, which rejects a raw pointer and returns 0.

Measured with gdb on the Stage 3 binary (hello-world build), `rt_hash_text` operand tag
by caller: `selected_key_put_v1` tag 1, `selected_key_position_v1` tag 1 then **tag 0**,
`module_surface_from_owner` **tag 0** (so every surface `content_hash` was 0),
`add_alias_canonical_identity` **tag 0**. The tag-0 lookup is the `for key in
index.lookup_keys` loop ending `module_surface_selected_exports_build_v1`
(`20.hir/hir_lowering/module_surface_selected_exports_v1.spl`): every row became -1 and
`module_surface_selected_exports_project_v1` indexed `source_surfaces[-1]`.

**Fix:** registry rows now also normalize the operand with `ensure_tagged_str` (no code
for a statically tagged local; otherwise one `rt_interp_cstr` word compare, boxing only
a raw operand). Identity owners (`rt_rc_*`, `rt_string_free`, `rt_heap_ref_wellformed`)
are excluded through `tagged_text_value_arg_is_identity`.

- Spec: `test/01_unit/compiler/mir/tagged_text_extern_raw_operand_spec.spl`
  (2 of 4 red before, 4 of 4 green after, seed interpreter).
- Fixture: `test/fixtures/native_tagged_text_extern_raw_operand/main.spl` — Stage 2
  `e4e072f8289` prints `for=0 for_param=0 / index=0 field_for=0 / table n=7 bad=7`;
  the seed interpreter prints 3603 and `bad=0`.
- `@workaround` at the crash site (indexed loop instead of the `for` binder), checked on
  the same Stage 2 with the fixture's table shape (`bad=0`).

## Defect 2 — raw text escapes a transient scratch scope (OPEN)

`_driver_resolve_entry_import_untimed` (`80.driver/driver_entry_closure_core.spl`)
returns the resolver answer after `rt_transient_heap_promote(answer)`. gdb on Stage 3:
4 of the first 400 returns were raw `char*` (tag 0). The generic `T` boundary boxes a
raw text as a copy, so promotion retains the copy and the caller keeps a pointer into
scratch memory freed at scope end. The path later reached
`_driver_file_natively_owns_v1` via `driver_preclosed_source_aliases_v1` (backtrace
taken in a parse-shard child) with allocator bytes in its tail.

- Fixture: `test/fixtures/native_transient_scope_raw_text_escape/main.spl` — Stage 2
  prints `plain=junk-... spl=false`; the owned variant is correct.
- `@workaround`: `+ ""` on the resolver answer (an owned tagged text is promotable).
- **Not done:** the raw producer inside `_driver_resolve_entry_import_exact` is not
  pinpointed, and there is no compiler fix. Candidates: keep the tagged element for
  `for` binders over `[text]`, or let promotion resolve a raw pointer to its owning
  string. Other scratch scopes that return text may have the same defect.

## Unproven until a new Stage 2 exists

- Both fixtures natively green with the fixed compiler.
- Stage 3 self-build passing the selected-export projection and running clean of
  `[explicit-source] rejected` lines; whether further defects sit behind these two.
