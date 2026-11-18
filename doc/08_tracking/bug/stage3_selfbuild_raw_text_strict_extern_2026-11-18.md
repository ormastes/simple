# Stage 3 self-build dies: raw `char*` text reaches strict tagged owners

- **Date:** 2026-11-18
- **Status:** defects 1 and 2 fixed in source (MIR-level proof; native proof needs a new
  Stage 2); defect 2 keeps its source workaround until then
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

## Defect 2 — the generic argument boundary copies a raw text (fixed in source)

`_driver_resolve_entry_import_untimed` (`80.driver/driver_entry_closure_core.spl`)
returns the resolver answer after `rt_transient_heap_promote(answer)`. gdb on Stage 3:
4 of the first 400 returns were raw `char*` (tag 0), and the path later reached
`_driver_file_natively_owns_v1` with allocator bytes in its tail.

**Root cause** — `lower_call_with_value`, the `HirTypeKind.Any | TypeParam` argument arm
(`50.mir/_MirLoweringExpr/switch_operators_calls.spl`), boxed a text argument with
`box_runtime_dictionary_key_v1` (`50.mir/_MirLoweringExpr/expr_dispatch.spl`). That
boxer keeps a tagged handle but sends every borrowed `char*` to `box_runtime_value`:
`rt_interp_cstr` + `rt_strlen` + `rt_string_new`, a copy. A `for` binder or `a[i]` over
`[text]` is exactly such a `char*` — the element's own data buffer. So
`rt_transient_heap_promote<T>(answer)` received the copy (allocated while the scope is
paused, hence already persistent: promotion "succeeds" as a no-op) and the caller
returned the original, freed at scope end. The runtime was never the gap:
`rt_core_transient_text_data_pointer` already resolves a raw data pointer to its
owning string, for roots and children.

**Isolation, Stage 2 `394e392ed55`, cranelift and llvm identical** (variants of the
fixture, each run after a 2000-string churn):

| scratch result | promoted through | native result |
|---|---|---|
| `for` binder | `rt_transient_heap_promote<T>` | wrong (reads reused memory) |
| `candidates[0]` | same | wrong |
| `for` binder | generic Simple wrapper `promote_any<T>` | wrong |
| call result (tagged) | same extern | correct |
| `for` binder `+ ""` | same extern | correct |
| `for` binder, `candidates[0]` | extern declared `(value: text)` — raw word passed | correct |

The last row is the discriminator: same producer, same runtime, no generic boundary.

**Fix:** the argument arm now calls `box_runtime_generic_argument_v1`. For a borrowed
`char*` above the nil/small-int floor it forms the owner candidate `(word - 16) | 1`
(`RtCoreString` header, `RT_VALUE_TAG_HEAP`) and keeps it only when
`rt_string_data(candidate)` answers the same word; `rt_string_data` checks registry
membership before reading any header. An ownerless `char*` (a literal) is copied as
before. Dict-key sites are unchanged. No runtime change.

- Spec: `test/01_unit/compiler/mir/generic_text_argument_owner_identity_spec.spl`
  (3 of 5 red before, 5 of 5 green after, seed interpreter): direct extern, generic
  wrapper, `for` binder; controls for a scalar argument and a dict key.
- Runtime contract: `check_generic_argument_owner_identity` in
  `src/runtime/test/rt_transient_heap_scope_selfcheck.c` runs the emitted sequence in C
  — candidate equals the original handle; interior word, literal, 0 and 3 are refused;
  the string promoted through its data pointer survives scope end while one whose
  boundary copy was promoted is freed. `SELFCHECK PASSED (0 failures)` on clang 23.
- Cost, C runtime, 2M boundary crossings of a 58-byte text: heap-owned 191 -> 14 ns
  per call and 244 MB -> 0 of copies; ownerless literal 203 -> 207..232 ns (one extra
  registry probe before the same copy).
- Fixture: `test/fixtures/native_transient_scope_raw_text_escape/main.spl` now carries
  the `index`, `direct` and `wrapped` variants (old Stage 2: `plain`, `index`,
  `wrapped` wrong; `owned`, `direct` correct).
- `@workaround` (`+ ""` on the resolver answer) stays until the fixture is green on a
  new Stage 2.

**Same shape elsewhere** — every scalar `text` handed to `rt_transient_heap_promote<T>`
/ `transient_promote<T>` crossed the copying boundary; whether it dangled depends on
the argument being raw at run time, which was measured only for the resolver answer.
All are covered by the compiler fix; no further workaround was added. Arguments that
are record fields, parameters or globals (representation unknown statically):
`20.hir/hir_lowering/module_surface_registry.spl:797-800` (`surface.*_name`),
`20.hir/hir_lowering/types.spl:1121`, `00.common/cache/reverse_reference_facts.spl:225-228`,
`10.frontend/frontend_shared_parse_cas_v1.spl:43-44`,
`10.frontend/core/representation_declarations_v1.spl:43-44`,
`10.frontend/core/_ParserDecls/enum_module_body.spl:1428-1429`,
`80.driver/driver_hir_cache.spl:749`. Locals (a call result is tagged and was
already safe; producers not inspected one by one): `80.driver/driver_source_parse_selected.spl:268,408`,
`driver_source_parse_streaming.spl:455,470`, `driver_hir_pipeline_lowering.spl:1013`,
`driver_worker_surface_closure_v1.spl:311`, `driver_types.spl:282`,
`native_capsule_mir_identity.spl:303`, `driver_mir_shard_export_v1.spl:70`,
`src/app/compiler_entrypoint/inventory_binding_scratch.spl:36`.

**Separate observation, not investigated:** a `struct` local built inside the scope,
promoted through a `fn f(answer: Holder)` helper and read after scope end, crashed
(`SIGSEGV` in `strlen`) even with a tagged field. The same read without a scope, and
with only a generic call, is correct. Not the text boundary; no fixture added.

## Unproven until a new Stage 2 exists

- Both fixtures natively green with the fixed compiler (defect 2: the emitted sequence
  is proven against the C runtime, the lowering only at MIR level).
- Stage 3 self-build passing the selected-export projection and running clean of
  `[explicit-source] rejected` lines; whether further defects sit behind these two.
