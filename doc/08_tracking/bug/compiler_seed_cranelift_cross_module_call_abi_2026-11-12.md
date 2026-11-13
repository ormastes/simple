# Seed Cranelift backend does not type-check cross-module call arguments (2026-11-12)

Status: open
Area: src/compiler_rust (seed cranelift backend) / bug p4p2_cranelift_verifier_types_2026-10-20

## Symptom

`test/02_integration/compiler/backend/cranelift_cross_module_call_abi_spec.spl`
builds two cranelift modules (provider + caller), links them with a C harness,
and runs them. The spec exists to guard bug `p4p2_cranelift_verifier_types_2026-10-20`:
the import signature for a cross-module call must come from the CALLEE's
declaration, not the caller's operands.

Under the Rust seed the bug reproduces — the fixture that passes an `i64`
where the callee declares `f64` is accepted and run instead of rejected:

```
✗ <case>
  expected int_to_f64 value=cv=1.500 rc=0 to contain
  arg 0 is i64 but the callee declares f64
```

i.e. `take_i64(2.0)` / `half_f64(3)`-style mismatches compile and execute
("silent garbage") rather than being diagnosed at build time.

## Root cause

The seed's cranelift backend does not apply the callee-declared parameter
types when importing a cross-module call (the exact defect the spec's header
describes for the pure-Simple side). The spec is behaving correctly — it is
catching a real, still-open defect in the seed backend.

## Unblock

Port/apply the verifier-types fix (callee-declared import signatures) to the
seed cranelift backend, or run this spec under the rebuilt pure-Simple
producer where the fix landed. Keep the spec RED until the mismatch is
diagnosed; do not weaken its assertions.

## DIAGNOSED 2026-11-13 (wave-2 deep-fix lane, work/compiler-seed-deepfix-20261113)

The record's area attribution is incomplete: the spec never touches the
Rust seed backend. It drives the PURE-SIMPLE
`compiler.backend.cranelift_codegen_adapter`
(`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`) via
`test/fixtures/compiler/cranelift_cross_module_call_abi/driver.spl`, and the
adapter ALREADY implements the verifier-types fix
(`cl_import_call_abi_error`, lines 1955-1995, emits
E-BACKEND-CRANELIFT-CALL-ABI exactly as the spec pins). Under the seed, 4 of
the 5 case lines pass TODAY: `match`, `match_i64`, `i64` ("arg 0 is f64 but
the callee declares i64") and `untyped` are all rejected/accepted correctly.
Only `int_to_f64` fails: `cv_half_f64(3)` is admitted and prints cv=1.500.

Root cause — a deliberate later commit regressed this case, not a missing
seed fix:

1. 2026-10-20 bf56b71044f "fix(cranelift): derive cross-module import
   signatures from the callee declaration" landed the fix AND this spec.
   Its message states the contract: "There is no implicit coercion."
2. 2026-11-07 085f1872947 "fix(mir): lower int literals in f32/f64 slots as
   float constants" added `lower_int_literal_for_float_slot`
   (src/compiler/50.mir/mir_lowering_stmts.spl:2843): an unsuffixed int
   literal flowing into a DECLARED float slot lowers as a float constant.
   It exists because Cranelift native builds failed the verifier with "arg 0
   has type i64, expected f64" for SAME-module direct calls.
3. The fixture driver lowers ONE module and splits it into provider/caller
   AFTER lowering. At lowering time `cv_half_f64(3)` is a same-module direct
   call, so the 11-07 coercion fires: the arg operand is an F64(3.0) const
   (verified with a probe printing the MIR operand types). The module split
   then hands the adapter a call whose arg is already f64, so the (correct)
   callee-declared ABI check sees f64 == f64 and admits it. The spec expects
   the int->f64 crossing to be REJECTED per the 10-20 contract.

Why no code fix in this lane: at MIR-lowering time the callee is module-local
(the split happens later), so the lowering cannot know the call will cross a
module boundary; the coercion is REQUIRED for same-module native calls (its
own docstring documents the verifier failure it prevents). Honoring both
contracts needs the coercion decision deferred to the backend (adapter
converts same-module, rejects imports) or the driver marking split-bound
calls -- a MIR-provenance/adapter redesign, not a lane-sized change. The spec
stays RED per this record's own instruction, now with a precise diagnosis:
revert-reason 085f1872947 vs contract bf56b71044f on cross-module int->float
literal arguments.

## FIXED 2026-11-13 (work/compiler-seed-remainders-20261113)

The lane-sized ABI-visible pin wave-2 asked for: the coercion stays at MIR
lowering (same-module native builds still need it), and the lowering now
records the crossing on the emitted call's signature so the adapter's
import check can still see it after the operand types read f64.

- `MirSignature.int_literal_coerced_params: [bool]` (mir_types.spl),
  index-aligned with `declared_params`: true when the call argument at that
  index was an unsuffixed int literal (or its negation) coerced into a
  declared f32/f64 (or Optional float) slot.
- The coercion predicate was split out of
  `lower_int_literal_for_float_slot` into the shared free fns
  `hir_unsuffixed_int_literal_value` / `hir_type_is_declared_float_slot`
  (mir_lowering_stmts.spl) so the pin and the coercion cannot disagree
  about which argument crossed.
- The direct-call lowering (switch_operators_calls.spl) marks the emitted
  `MirSignature`; `direct_call_operand_with_return_type` carries the pin
  through its field-by-field signature rebuild (the one transport point
  that would otherwise drop it).
- `cl_call_abi_mismatch` (cranelift_codegen_adapter.spl) consults the pin
  in the known-signature arm and rejects with the pinned wording:
  `arg {index} is i64 but the callee declares f64; convert it explicitly
  at the call site`. Same-module paths never read the pin (byte-identical
  behavior); the LLVM lane is untouched.

Evidence (seed binary, fixture run.shs, before -> after):
- before: `int_to_f64 value=cv=1.500 rc=0` (admitted silently)
- after:  `int_to_f64 compile-error=rc1 E-BACKEND-CRANELIFT-CALL-ABI:
  ... arg 0 is i64 but the callee declares f64; ...`
- after, all five case lines match the spec oracle exactly: untyped/i64/
  int_to_f64 rejected, `match value=cv=1.500 rc=0`,
  `match_i64 value=cv=42 rc=0`.

Known gaps (documented remainders, out of scope here): the pin is recorded
only for direct-call lowering; method-call and `exact_extern_signatures`
int-literal float-slot crossings keep today's admit-behavior. The pin is a
call-site provenance record, not a general MIR int->float provenance
redesign.
