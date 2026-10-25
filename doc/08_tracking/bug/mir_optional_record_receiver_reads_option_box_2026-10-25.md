# MIR: a `T?` record receiver reads the Option box (O1) (2026-10-25)

Status: FIXED in the compiler on work/p3fix-o1a1 (45d8e519060). It takes
effect when the Phase 3 compiler rebuilds itself. The source workarounds stay
until then.
Found by: Phase 3 sweep, class O1. O1 is the umbrella for L1 (lost loop
accumulators) and X3. Census: 72 heuristic sites in
S/r27/sweep/o1_census.txt.
Related: nil_narrowed_option_field_read_skips_unwrap_2026-10-25.md (the L1
workaround, work/p3fix-l1) and mir_no_flow_narrowing_optional_container_2026-10-25.md.

## Symptom
```
fn find_pt(xs: [Pt], want: i64) -> Pt?:   # `return p` on a hit
fn k_narrow(t: Pt?) -> i64:
    val found = t
    if found == nil:
        return -1
    found.k            # Stage 2 output: 4 (the box header kind), want 9
```
A `-> T?` producer returns the canonical Option box (enum id 1, Some = 0,
payload in word 3). MIR has no flow typing, so after the nil check `found`
still has type `Optional(Pt)`. The Field arm emitted `GetField` directly on
the box and read the header word.

## Root cause
The Field-read arms (expr_dispatch.spl, both the disc-guarded pre-dispatch
and the main `case Field` arm), the field-store arm (mir_lowering_stmts.spl
`lower_assign` Field), and the mutating-method writeback base
(method_calls_literals.spl) all used the lowered receiver local as the record.
Nothing unwrapped an Optional record receiver. Scalar optionals
(`option_scalar_payload_of`) and text optionals (`narrow_optional_text_receiver`)
already had a use-site unwrap. Records did not.

## Fix (option (a), no flow analysis)
`option_record_receiver_payload_v1(receiver, local)` (method_calls_literals.spl):
- If the receiver's HIR type, or the local's remembered type, is
  `Optional(Named(S))` and S is a struct or class with a registered layout,
  emit `rt_unwrap_or_self(local)`.
- Give the payload local S's HIR type and layout provenance
  (`struct_value_syms`), so field indexes resolve as they do for a plain
  record local.
- Every other receiver, and every array receiver, is returned unchanged.

`rt_unwrap_or_self` is the `if val` / `??` unwrap. It returns the payload for
the canonical Option, and the word itself for anything else (a raw record
pointer, or nil). So the fix is sound on both the boxed and the flat lane.
It accepts no new programs and widens no nil. A raw nil receiver stays nil
and faults on the read as before. A None BOX receiver used to read its header
word silently. It now unwraps to nil and faults, so it fails louder.
Cost: one `rt_unwrap_or_self` call per field access on a `T?` local narrowed
by `== nil`. A local bound by `if val` has type `T` and is unaffected.

Not changed: a method call on a `T?` receiver (`t.k_plus(1)` after a nil
check). That already fails closed with the MIR error `unresolved method call`
(measured on Stage 2). It is not a silent misread.

## Evidence
- Red, Stage 2 p2shard-17 (`S/r27/stage2-simple`), entry-closure
  native-build, aarch64 cranelift:
  - `k_narrow` hit gives `4` (want 9). 4 is the heap-enum kind in the box
    header.
  - `x_nested` (`t.inner.x`) SEGVs in `app.zz_o1a1.o1.x_nested`, because the
    header word is dereferenced as `Inner`.
  - `k_store` gives 42 only because the store and the read both hit the same
    box word, so the box itself is corrupted.
- The spec test/01_unit/compiler/codegen/native_optional_record_receiver_unwrap_spec.spl
  embeds the same program.
- Green needs a compiler that contains this fix (see "Verification").

## Workarounds that stay
The Stage 3 binary's own code is compiled by the unfixed Stage 2. So the
compiler-internal if-val workarounds on work/p3fix-l1 (mir_type_is_scalar_numeric,
box_runtime_value, local_is_f32) remain necessary until a compiler built
WITH this fix rebuilds itself. Delete them after that self-build.
The 69 app and lib census sites need no source change: they are compiled by
the fixed compiler.

## Verification
The fix only takes effect in code that a compiler containing it produces.
Recipe: build Stage-2 `.o` files of `compiler.mir._MirLoweringExpr.expr_dispatch`,
`compiler.mir._MirLoweringExpr.method_calls_literals` and
`compiler.mir.mir_lowering_stmts` from this branch merged with work/p3fix-l1.
Relink them into the Phase 3 bypass Stage 3, then native-build the probe with
that binary.

## Scope notes (A1, same branch)
Array `==` now compares length plus elements through rt_native_eq. Scalar,
text, nested array and enum elements compare by value. `[Struct]` elements
still compare by pointer: rt_core_value_eq_inner has no struct lane. That is
no regression from the old identity compare.

Measured 2026-10-25 on `S/o1a1/simple.o1a1`, the probe24 bypass relinked with
those three objects plus the L1 instantiation shim (0 undefined symbols). The
control is the plain `S/r27/bp/simple.probe24`.

| probe | probe24 (control) | simple.o1a1 (fixed) |
|---|---|---|
| O1: `T?` field read, nested read, store | SEGV in the produced binary | `narrow hit=9 miss=-1`, `nested hit=90 miss=-1`, `store hit=42` |
| A1: equal `[i64]`, `[text]` (one side concat), `[u8]` | `eq=false ne=true` for every pair | `eq=true ne=false`; unequal pairs `eq=false ne=true` |

The O1 probe passes its two records as parameters. A `for p in xs` loop over
`[Pt]` crashes BOTH binaries in `remember_array_index_projection_provenance` ->
`result_err_layout_identity`. That is a pre-existing Stage 3 defect of class
X1, not this fix. The first two entry-closure builds on simple.o1a1 crashed
in the MIR worker. The crash did not reproduce in any of the four runs that
followed: two plain runs, one under gdb, and the O1 run. All four produced
correct output.
