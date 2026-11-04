# MIR bare-variant / enum spec cluster (2026-11-04)

Seed `simple-ref`, one spec per run. RED: 5 specs failing.

## Fixed
1. Spec-stale: `bare_variant_retained_subject_spec`, `lambda_lift_if_enum_capture_scan_spec`
   asserted an empty error list, but a no-default enum match records the staged
   non-fatal diagnostic `non-exhaustive enum match on '...'`
   (`switch_operators_calls.spl` ~5182, `self.error`, since b2d42b02ecc 2026-08-01;
   warning now, error after phase 3). Both specs now filter exactly that text
   (precedent: `mir_option_result_qualified_field_spec.spl`).
2. Product bug (masked by 1): `lower_lambda_value_for_type` (same file, ~8169/8188,
   introduced by 770de8344fa "propagate fatal lifted-body errors") treated ANY
   child `lw.errors` entry as fatal, so a non-fatal warning in a lifted lambda
   body aborted the lift ("cannot materialize lambda for its declared function
   slot"). Now only `MirError.fatal` aborts; warnings propagate to the parent.

## Fixed (lane l2-enumrecv, 2026-11-04)
- `bare_variant_untyped_subject_reject_spec`: product bug. The unique-owner
  fallback in `lower_match_case_unchecked` (expr_dispatch.spl, "site-19") fired
  even when the subject type was KNOWN to be a registered enum lacking the name
  or a non-nominal type (`i64`), so `case Return:` over `op: Op` borrowed
  `Kind.Return`. Now only taken when the subject type is absent or a Named type
  with no registered owner (the site-19 shape).
- `bare_variant_unit_self_subject_spec`: spec stale. Contract (also pinned by
  `enum_match_wildcard_order_lowering_spec`): one `ematch_arm` per enum arm, the
  wildcard is the default and gets none. Expected 2/3 -> 1/2.
- `bare_variant_retained_subject_spec` (undeclared arm): spec stale. The subject
  `first.kind` is now typed, so the untyped-only retained-owner shape check is
  not reached; the typed route rejects loudly with
  `enum match: 'KindA' has no variant 'Literal'`. Assertion moved to that text.
- `enum_subject_owner_recovery_spec`: product bug. A present `text` / record
  local with a remembered concrete type was vetoed (`remembered_concrete_negative`)
  for a `T?` slot. New `enum_payload_present_fills_optional` (heap-handle
  payloads only: text, class/struct/enum) accepts it; wrong-record/nil cases
  still rejected.
- `match_guard_invariant_acceptance_spec`: spec stale. `case (R, R)` now resolves
  `S.R` (bare_unit_variant_in_tuple_pattern_binds_2026-10-10.md is FIXED); the
  spec flips to its own documented "becomes 0" expectation.
- `i64_receiver_to_text_binding_spec`: spec stale; only the staged non-exhaustive
  warning (filtered by exact text, as in mir_option_result_qualified_field_spec).
- `to_i64_binop_receiver_spec`: erased `Any` receiver lowers via
  `rt_to_int_dynamic` (parses a heap string, identity otherwise), not
  `rt_string_to_int_lenient`; assertion moved to the dynamic parse.
- `methods_mir_receiver_shapes_spec`: product bug. Since 87aaaa999c7 an untyped
  HirExpr carries a Unit placeholder in `type_`; the erased text-builtin arm read
  `receiver.type_` as present. Now gated on `receiver.has_type_`.
  Audit (2026-11-05) of the other `receiver.type_` reads in the same file:
  the six `if val x = receiver.type_` probes (~2594 Str, ~3603 Int, ~3730 /
  ~3912 / ~3955 / ~4250 Array|Slice) only SET a flag on a positive match and
  fall through on `case _`, so the Unit placeholder behaves exactly like an
  absent type -- benign, left as is, pinned by the "audit pin" case in
  methods_mir_receiver_shapes_spec. The discriminating criterion is an `else`
  branch: the fixed arm had one (`erased_recv_ty_ok = true` when untyped). One
  more site had the same defect shape: the write-back `receiver_type` probe
  (`val maybe_receiver_type_for_call = receiver.type_; if ... != nil`, ~2841)
  admitted the placeholder, so `xs[0].push(1)` / `p.items.push(1)` over an
  untyped `xs` / `p` typed the GEP/load/get_field of the receiver slot as Unit
  instead of the documented i64 default (measured: MIR local `ty="Unit"`,
  `Ptr{pointee: Unit}`). Gated on `has_type_` (the `receiver_is_dict` probe
  ~3021 shared the variable and is converted the same way; it was benign).
- `to_i64_binop_receiver_spec` (correction): with the `has_type_` gate above, a
  declared `Any` receiver is admitted by the erased arm and, being a
  runtime-value local, `to_i64` lowers to the tagged conversion owner
  `rt_any_to_int` (parses text, unboxes numbers) -- not `rt_to_int_dynamic`.
  The 2026-11-04 spec edit was measured against the pre-gate product and was
  red at the commit (`reg_before`: 5/6); assertion moved to `rt_any_to_int`
  with both raw text parses asserted absent.

## Open (not fixed)
- `bare_variant_retained_subject_spec` (2 of 6 red at HEAD, not 1):
  - `case mut Leaf:` fails in the core parser (patterns are parsed by the
    expression parser; no `mut` pattern prefix). NOT implemented 2026-11-05 on
    purpose: `case mut x:` appears in no language doc (syntax quick reference,
    doc/07_guide/language/*, doc/06_spec, grammar) -- only the Rust seed parses
    it (`parser_patterns.rs:260`, `Pattern::MutIdentifier`) and the AST/HIR
    thread the flag (`PatternKind.Binding(name, is_mut)` ->
    `symbols.define(..., mutable)`). Needs an owner decision to document the
    form first. Full scope once decided: a `__mut_binding(x)` marker next to
    `parse_match_region_marker` (same raw-source binder lookahead; `mut` lexes
    as an identifier), `convert_flat_pattern` -> `Binding(name, true)`, AND a
    gate in expr_dispatch.spl ~7707 (`case Binding(bsym, _)` reclassifies a
    bare name into a variant test regardless of the mut flag, unlike
    switch_operators_calls.spl:4054), plus a grammar-doc line.
  - `rb` ("re-owned unit-variant arm whose body names the binding reads the
    subject"): `mir: undefined variable Leaf`. Root cause: expr_dispatch.spl
    ~7755 rewrites the Binding arm into `HirPatternKind.Enum(.., "Leaf", None)`
    BEFORE the scrutinee local exists and drops `bsym`, so the body's
    `Var(Leaf)` is never bound; lower_enum_match_flat's own re-own loop
    (switch_operators_calls.spl:4046-4077, which binds `own_sym` to
    `scrut_local`) only sees arms that are still Bindings.
    **FIXED 2026-11-05 (later the same day):** no new field -- the
    reclassification loop in `lower_match_case` (expr_dispatch.spl, the
    `case Binding(bsym, _)` arm) collects each reclassified `bsym.id` into
    `reowned_binding_syms`, passed as a new defaulted trailing parameter
    through `lower_enum_match` (all three of its `lower_enum_match_flat`
    calls forward it) into `lower_enum_match_flat`, which binds every id to
    `scrut_local` (`local_map` + `bind_local`, exactly like its own re-own
    loop) right after `lower_expr(scrutinee)`. A parameter rather than a
    field so a nested match inside the scrutinee cannot consume or clobber
    it. The two other `lower_enum_match` callers (semantic-capture and
    explicit enum-only routes) pass unreclassified arms and use the default
    `[]`. Spec 4/6 -> 5/6 (`rb` green, 3 variant tests); the only red left
    is `case mut Leaf:` above, which stays unimplemented on purpose. 11-spec
    50.mir regression set (bare_variant_*, enum_match_*, generic_struct_*)
    identical before/after.
- `trait_typed_receiver_dispatch_spec` (10 of 11 red): the spec pins stage2
  devirtualization (`lower_trait_receiver_method_call`), but since ac6c0a021c5b
  (2026-10-12) `lower_method_call` routes every declared trait-typed receiver
  through the native trait object ABI (`lower_native_trait_method`, vtable
  `CallIndirect`) BEFORE the devirt path, so no `Mem.list` call, `rt_panic`, or
  multi-implementor error is produced. Needs a decision: delete the devirt path
  as dead code and rewrite the spec to the native ABI contract, or gate native
  ABI so the whole-closure lane still devirtualizes. The 2026-10-30 additions
  were "authored, not executed" (see bug doc ..._lifted_scalar_trait_context_2026_10_30.md).

## Follow-up
- Lift now aborts on `mir_error_is_fatal` (flag or legacy-text allowlist, shared with
  the driver owner). `expr_dispatch.spl:625` ("cannot lower ... as a function value")
  emits a placeholder const 0 as a non-fatal error: promote it to `error_fatal`.
