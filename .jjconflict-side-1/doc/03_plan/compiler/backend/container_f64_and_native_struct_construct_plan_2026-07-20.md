# Container-f64 lossless + native-build struct-construct fix

- **Created:** 2026-07-20
- **Domain/topic:** compiler / backend (native-build correctness)
- **Related:** [native_entry_build_correctness_2026-07-14](native_entry_build_correctness_2026-07-14.md),
  [native_build_open_bugs_plan_2026-07-15](native_build_open_bugs_plan_2026-07-15.md)

## Goal

`f64` routed through the tagged `RuntimeValue` representation (array/dict/`Any`
elements, struct fields, enum/Option payloads) must be **lossless on both
compiler paths**, and `native-build` must compile programs that define and
construct structs. Historically container floats lost the low 3 mantissa bits
(`[0.1][0] != 0.1`) and native-build could not build any struct.

## Done (landed on origin, verified)

| Item | Commit | Coverage |
|------|--------|----------|
| Interp/JIT heap-box (Rust `simple_runtime`) | `aa7ae5506c6` | array/dict/scalar/for-in/print/struct-field/Option all lossless on `run`/`test` |
| Native-build heap-box port (`runtime_native.c` `RtCoreFloat` + `expr_dispatch.spl` `rt_value_float`/`rt_value_as_float`) | `f33dc52320f` | array/dict-value/dict-key/scalar/for-in/print lossless on native-build |
| Native-build struct-construct BUILDFAIL fix (`driver_pipeline.spl` missing `MirLowering` fields) | `0faa51502fd` | any local struct construction on native-build; guard `test/03_system/native/struct_construct_native.spl` |

Discrimination is O(1) (registered-pointer HashSet, membership tested before
deref → guards the tag-collision SEGV class); reads are dual-aware (heap +
legacy inline); float dict keys canonicalized to the inline form.

## Struct-construct native-build BUILDFAIL — root-caused, fixed, and landed

`native-build --entry` on **any** local struct construction failed with
`error: semantic: method has not found on type nil`. Landed as `0faa51502fd`
(guard: `test/03_system/native/struct_construct_native.spl`) — folded into the
"Done (landed on origin, verified)" table above.

- **Root cause:** `driver_pipeline.spl`'s `direct_lowering` builds its
  `MirLowering` from a **hand-duplicated copy** of the canonical
  `MirLowering.new_for_target` constructor that had **drifted, omitting 8
  fields**: `struct_field_has_default`, `struct_field_default_expr`,
  `struct_field_hir_type`, `runtime_value_locals`, `option_value_locals`,
  `nil_locals`, `enum_runtime_id_index`, `enum_runtime_id_names`. The seed
  interpreter **silently nil-fills** any struct-init field omitted from a
  constructor call (it does not error at construction — same landmine documented
  for `global_static_ids` in `mir_lowering_types.spl`), so those fields read back
  `nil` and the first `.has(...)`/index on one crashed MIR lowering. Native-only
  because `run`/`test` use the Rust HIR/MIR lowering, not this `.spl` path.
- **Fix:** add the 8 missing fields to the inline constructor + a sync-guard
  comment (ideally collapse the copy into a `new_for_target` call later).
- **Verified:** `sfix=30`, `n_sctor=30` (construct-only), i64/f64-field repros.

## Remaining (all closed 2026-07-20)

1. Confirm the struct-f64-field repro returns 30 on native (struct-field case is
   jointly unblocked by the heap-box port + this struct fix). **DONE:** CONFIRMED
   at origin tip — `Q(v: 0.1); q.v == 0.1` → rc 30 on native-build; guard
   extended: `test/03_system/native/array_f64_element_precision.spl` now also
   asserts a struct f64 field.
2. **Land the struct fix** onto current origin tip (clobber-safe plumbing):
   `driver_pipeline.spl` + new guard `test/03_system/native/struct_construct_native.spl`
   + RESOLVED banner on `native_build_entry_struct_construction_buildfail_2026-07-20`.
   **DONE:** landed (`0faa51502fd`).
3. Update `seed_f64_array_element_precision_mask` — struct-field native case is
   now unblocked (was recorded as blocked by a separate pre-existing bug).
   **DONE:** `seed_f64_array_element_precision_mask_2026-07-19.md` updated —
   struct-field case resolved, only Option-payload case remains open (separate
   bug).
4. **Follow-up (recurrence prevention):** collapse the duplicated
   `MirLowering(...)` in `driver_pipeline.spl` into a `new_for_target` call so the
   drift class cannot recur (verified behavior-equivalent; deferred only to avoid
   a full-bootstrap re-gate in this change). **DONE:** BOTH hand-duplicated
   `MirLowering(...)` copies in `driver_pipeline.spl` (the --entry-closure one
   AND a second, even-further-drifted copy on the fallback lowering path that
   still had the live nil-fill landmine) are collapsed into
   `MirLowering.new_for_target(SymbolTable.new(), target_context)`; verified
   behavior-equivalent (native repros + full native-smoke-matrix).

## Hardening addendum (2026-07-20, later session)

A further sweep after landing the struct fix found one more container-f64 gap,
fixed in this session:

- **Found:** empty-container element-type erasure. An empty `{}` / `[]` literal
  fixes the container's declared element type at the i64 default
  (`lower_dict_lit` default, `method_calls_literals.spl`); stores heap-box an
  f64 by VALUE type, but reads/print/`==` decode by the CONTAINER's declared
  type → the integer `>>3` arm shredded the heap-box pointer:
  `var d = {}; d["k"] = 0.1; print(d["k"])` printed a raw pointer
  (`13668775811778`) and `== 0.1` was false; same for
  `var a = []; a.push(0.1); a[0]`.
- **Fix (native lowering, `.spl`):** new `MirLowering.runtime_elem_value_type:
  Dict<i64, MirType>` side-table — store sites (`d[k]=v` rt_dict_set,
  `a[i]=v` rt_array_set, `a.push(v)`) record the f64/f32 MIR type of the
  stored value keyed by the container local id (`note_container_elem_type`,
  `expr_dispatch.spl`); the dict and array index reads consult it ONLY when
  their statically resolved element type is the erased i64 default, so
  declared-i64 containers are unaffected. Decoded locals then carry F64, so the
  existing type-driven print/`==` paths work unchanged. Reset alongside
  `runtime_dict_locals` (3 sites).
- **Still open** (interp/`run` path, Rust `simple_runtime`, needs seed rebuild +
  redeploy — walled on user go-ahead): store-side inline BoxFloat precision
  mask on `a.push(0.1)` and `a[i] = 0.1` (both rc 40 under `run`; dict literal
  and dict store are lossless there). Recorded in
  `seed_f64_array_element_precision_mask_2026-07-19.md`.
- **Also note:** `native_cache` can be poisoned by a failed build (a "cache
  hit" whose object file was never emitted → ld "cannot open ...o"); workaround
  `--clean` + unique source name; pre-existing, not addressed here.

## Out of scope (separate pre-existing native-build defects)

- Native `.?`/if-val Option unwrap leaks the Some tag, not the payload (wrong for
  `i64? = 7` too) — `hosted_native_option_try_unwrap_payload_leak_2026-07-19`
  (root `d71449a`).
- Dict **type annotation** on native --entry (`{text: i64}` → "Dict type expects
  2 type arguments") — surfaced during isolation testing; not addressed here.

## Deploy

`bin/release` redeploy of the self-hosted binary needs explicit user go-ahead;
not part of this plan.
