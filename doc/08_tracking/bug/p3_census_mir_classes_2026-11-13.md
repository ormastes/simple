# Phase-3 census (run-19 Stage 2): MIR failure classes (2026-11-13)

Census: `native-build src/app/cli/bootstrap_main.spl` (entry closure, 1619
modules, cranelift, go-to-end, 2 MIR workers) with the run-19 Stage 2 compiler
(`bootstrap-fable-19/.../stage2-admitted/simple`, pinned source `3197fdaa5ed6`)
over the `8cbab25851e` snapshot. HIR 1619/1619; MIR 1618 ok, 3 modules fatal.
Log: `simple-census-20261113/build/p3-census.log`. Fix lane: branch
`work/census-mir-fixes-20261113` (base `dc14e46a737`).

Discriminator used for every class (not a native build, <1.3 GiB, seconds):

    SIMPLE_LIB=<worktree>/src <stage2-admitted>/simple compile <probe>.spl --format=smf -o /tmp/x.smf

`compile` runs the same MIR lowering as the census; the LLVM `llc` step that
follows it fails on this host ("Metadata id is already used") for whole-module
closures and is unrelated (the census is cranelift). Verdict = presence of
`[mir-module-failure]` / `[first-compile-error] MIR lowering error`.

## Class 1 — `is_none` on a `text.to_i64()` result (persisted_graph.spl:96)

`unresolved method call: is_none ... owner= struct_method_syms=no` at
`priority.is_none() or memory.is_none()`, where `priority = fields[3].to_i64()`.

Root cause: `text.to_i64()` is the LENIENT raw-`i64` parse everywhere below
the interpreter — MIR records its result as `Int(64)` on purpose
(`50.mir/_MirLoweringExpr/method_calls_literals.spl` text-special arm:
"`"3".to_i64() ?? d` must not test raw 3 as the nil sentinel"), the C runtime
returns 0 on failure (`rt_string_to_int_lenient` -> `rt_string_to_int`), and
the seed HIR types it `I64`. Only the seed INTERPRETER returns nil on failure
(`interpreter_helpers/method_dispatch.rs:199`). So `.is_none()` on it has no
owner; the compiler is right to refuse. The site was written by `c1e50059d2c`
(safe-code `== nil` -> `.is_none()` sweep) and the `== nil` it replaced was
already vacuous natively. The strict `Option<i64>` parse that all three legs
agree on is `parse_i64()` (`rt_string_parse_int` returns nil on failure; MIR
records `Optional(Int)`; interpreter `string.rs:410`).

Fix: source — `fields[3].parse_i64()` / `fields[5].parse_i64()`.
Spec: `test/01_unit/compiler/action_graph/persisted_graph_decode_row_spec.spl`.
Probe: `to_i64().is_none()` red (same error text), `parse_i64().is_none()` green;
whole `persisted_graph.spl` closure (66 modules) MIR-clean after the fix.

**Recorded, not fixed (language-level):** `text.to_i64()` returns nil on failure
in the interpreter and 0 natively. The idiom `x.to_i64() ?? d` (795 sites under
`src/`) therefore cannot see a failure natively (per the text-special arm's own
comment, "`"3".to_i64() ?? d` must not test raw 3 as the nil sentinel"; the
`??` lowering itself was not traced here), and `x.to_i64() == nil` compares a
raw integer with the nil word. A `.is_none()` on a non-Optional receiver should be a HIR type
error; today it surfaces only as this MIR fatal. Owner decision needed: make
`to_i64` a real `i64?` (runtime + MIR representation change) or lint the
`?? d` / `== nil` / `.is_none()` forms on its result toward `parse_i64()`.

## Class 3 — `HirStmtKind.Let` payload 1 typed `HirType?` (statements.spl, 3 sites)

`enum construction 'HirStmtKind.Let': payload type mismatch at 1` at the three
`HirStmtKind.Let(symbol, binding_type, init)` constructions
(census snapshot lines 1067 / 1191 / 1231; tip 1106 / 1230 / 1270).

Shape: `val hir_type = if has_annotation: self.lower_type(t) else: nil` then
`val binding_type: HirType = if has_annotation: hir_type else: payload(..)`.
`hir_type` is a nullable merge; the join for `binding_type` is `HirType?`, and
HIR records THAT for the annotated symbol — `SIMPLE_ENUM_PAYLOAD_TRACE=1` on the
probe: `expected='named#0' remembered='named#0?' source='named#0?'`. MIR then
refuses a `T?` word in a non-optional payload slot (never widen nil). Probes:
bare-arm join red (also red with `hir_type: HT?` + `None`); `val x: HT =
lower(..)` green; `if val annotated = hir_type: annotated else: ..` green.

Fix: source — the three joins unwrap through `if val annotated_type = hir_type:`.
Behaviour is identical when `lower_type` yields a value; a nil from `lower_type`
under an annotation now falls to `binding_payload_type` instead of constructing
a Let with a nil type word.
Spec: `test/01_unit/compiler/mir/annotated_let_from_optional_arm_spec.spl`.

**Recorded, not fixed (HIR):** an annotated `val x: T = <if-join of T? and T>`
is typed `T?` by HIR — the annotation is dropped silently and the nullable
widening is neither reported by HIR nor by the HIR census; only the MIR payload
check catches it, and only when `x` flows into an enum payload. The pre-existing
`else: nil` arms in safe code at statements.spl:1082/1204/1239 remain
`never-widen-nil` debt (the Let `type_` slot is a plain nullable by design,
see the comment block above line 1043).

## Class 4 — `MirConstValue.Str(i64)` (synthetic_driver_codegen.spl:77-78)

`enum construction 'MirConstValue.Str': payload type mismatch at 0` at
`manifest_fields["driver_class"] = MirConstValue.Str(manifest.driver_class)`
and `...Str(manifest.vendor)`. `DriverManifestAttr.driver_class` and `.vendor`
are `i64` (`00.common/_Attributes/decl_attrs.spl:137-138`); the payload check
is correct. The constant is consumed only as an opaque `MirConstValue.Struct`
(`mir_instruction_graph.spl` renders it `zeroinitializer`), so no consumer
expected text.

Fix: source — `MirConstValue.Int(..)` for both. Probe red with `Str(i64)`;
whole `synthetic_driver_codegen.spl` closure (143 modules) MIR-clean after.
Spec: `test/01_unit/compiler/mir/synthetic_driver_manifest_const_payload_spec.spl`.

## Class 2 — bare struct names re-registered with different field lists

`[mir-lower] WARNING: struct/class name 'X' re-registered with a DIFFERENT
field list (...; keeping EXISTING)` for `JoinPoint` ([kind, kind_function_name,
kind_signature, kind_location, kind_error_type, block_id, instruction_index,
context] vs [kind, source_symbol, target_symbol, logical_join_point_id]),
`TextSpan` ([start, end] vs [value, start, len]) and `ElfSymbol`
([st_name, st_info, st_other, st_shndx, st_value, st_size, name] vs
[name, sym_bind, sym_type, section_index, value, size]). These are the only
three names in the whole census log.

State at both the pinned source and the tip: the registry already has a
module-qualified tier (`composite_layout_key` / `declared_struct_layout_key`,
`module_lowering.spl:838-920`), the bare tier is first-wins, the conflicting
bare name is recorded in `struct_field_order_conflict_warned`, and the main
read paths fail closed on it (`struct_value_layout_key`, `resolve_field_index`
`function_lowering.spl:2143-2300`). So the warning is a canary, not itself a
miscompile.

Audit of all 103 reads of the `struct_field_*` dictionaries under 50.mir
(89 `[..]` + 14 `.get(`): 9 qualified, 27 guarded, 47 registration-side,
**20 UNGUARDED bare-name reads**, reached two ways:
(A) `struct_value_syms` holds a bare name (writers `switch_operators_calls:1603`,
`expr_dispatch:1394/2110/2111/3504`, bare fallback of
`struct_value_provenance_key`); readers `mir_lowering_stmts:716-719`
(field count sets the aggregate copy size), `:1093-1095`, `:1142/1152/1157/1169`
(array-move copy skipping), `expr_dispatch:2017/2061-2064` (struct equality
loop), `provider_metadata:1382-1383` (method-receiver typing).
(B) `struct_field_type_name` stores the BARE nested field type name
(`module_lowering:1790`); the recursive struct copy (`mir_lowering_stmts:772`)
and equality (`expr_dispatch:2080/2112`) follow it with `.contains` only, so a
correctly qualified outer struct with a `TextSpan`/`JoinPoint`/`ElfSymbol`
field still copies/compares the nested value with the FIRST-registered layout.
Also `module_lowering:4338/4357` (prescan, bare) and bare writes outside the
conflict detector (`module_lowering:3333/3493`, `declaration_inventory_barriers_v1:53`,
`bootstrap_type_registration:62/137/162/181`).
Conditionally unguarded: `lower_struct_construct` (`switch_operators_calls:6620-6771`)
when the callee symbol is unresolved (`:9166` passes the bare `direct_name`).

Decision (this lane): fix the two recursion ROOTS, not the 20 reads.
`copy_struct_value_recursive` (`mir_lowering_stmts.spl`) and
`lower_struct_structural_eq` (`expr_dispatch.spl`) (a) fail closed with
`error_fatal` when their layout key is a bare name in
`struct_field_order_conflict_warned`, and (b) recurse into a nested record
through the module-qualified layout recorded per field in
`struct_field_type_ownership_key` (= `composite_layout_key` of the field type,
`module_lowering.spl:1790`) folded by `declared_struct_layout_key`, keeping the
bare name only for the symbol lookup. Both re-entry claims of the audit were
verified by reading the recursion sites (`:772`, `:2112`). Blast radius: only
names in `conflict_warned` fire -- three in this census -- so the next census
may trade a silent copy/compare of `JoinPoint`/`TextSpan`/`ElfSymbol` reached
through bare provenance for a loud per-module fatal naming the layout.
Spec: `test/01_unit/compiler/mir/same_named_struct_layouts_across_modules_spec.spl`
(+ `test/fixtures/compiler/same_name_layouts/span_{a,b}.spl`), interpreter-green,
UNEXECUTED natively: a 50.mir change cannot be executed in this lane (the census
compiler carries its own MIR; no Stage 2 rebuild). Load/parse evidence: a
MIR-loading seed spec (`array_projected_receiver_types_spec.spl`) runs 6/7 with
and without the change (the 1 failure is pre-existing on the base).

Remaining unguarded sites, NOT fixed here (named gaps): `mir_lowering_stmts:1093-1095`
(array move ctor count), `:1142/1152/1157/1169` (array-move copy skipping),
`provider_metadata:1382-1383` (method-receiver typing), `module_lowering:4338/4357`
(prescan), `switch_operators_calls:9166` (bare `direct_name` for an unresolved
callee), and the bare writers outside the conflict detector listed above.
