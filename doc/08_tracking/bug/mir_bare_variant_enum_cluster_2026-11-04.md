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
  `receiver.type_` as present. Now gated on `receiver.has_type_`. Six more
  `if val x = receiver.type_` sites in method_calls_literals.spl have the same
  shape and were NOT audited.

## Open (not fixed)
- `bare_variant_retained_subject_spec`: `case mut Leaf:` fails in the core parser
  (patterns are parsed by the expression parser; no `mut` pattern prefix). The
  Rust seed accepts `case mut x`. Ahead-of-feature: needs a `__mut_binding`-style
  marker in parser_stmts.spl + convert_flat_pattern (Binding(name, true)).
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
