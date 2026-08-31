# Coverage-wrapper native compile: HIR-lowering residuals (2026-08-31)

Status: OPEN (residual classes). Three sibling root causes were FIXED in the
same change (`fix/cov-wrapper-hir-lowering`); this record covers what is left.

## Context

A full suite run (`/tmp/suite3.log`, 1365 PASS / ~220 FAIL) had 27 `HIR
lowering: ...` failures plus 1 `Trait coherence errors`, all raised while
compiling generated coverage wrappers
(`spipe_wrapped__..._simple_cov_..._spec_native.spl`). Unlike PR #156 these are
NOT one injected-preamble cause: they split into at least eight independent
root causes.

## Harness (reproduction)

Wrappers are regenerated with `preprocess_spipe_native_result_file`
(`src/lib/nogc_sync_mut/test_runner/test_result_wrapper.spl:582`) and compiled
with `bin/simple compile <wrapper>`, reading the compiler's own exit status. A
green `bin/simple test --coverage` verdict is NOT evidence (the runner degraded
to the interpreter silently until PR #157).

Both sides were measured on seeds built from this branch's base
(`b0be388ec46`), pristine vs. patched — NOT the ambient `bin/simple`, which on
this host is built from uncommitted `lowerer.rs`/`identifiers.rs` edits and is
therefore not origin/main's compiler.

24 of the 29 rows reproduce their exact suite diagnostic through this harness.

## FIXED in this change (evidence)

1. **Paren-less builtin method call on a builtin receiver.**
   `xs.len`, `s.trim`, `xs.first` reached
   `cannot infer field type while lowering <fn>: struct 'Array' field 'len'`
   because `has_known_method_for_struct_name` consults only
   `method_return_types` (user-declared methods); builtin methods are never
   registered there, so the paren-less-method fallback was never reached.
   `Array`/`String`/`Dict`/… have no user-declarable fields, so `recv.name` on
   one of them is always a method call.
   Proof: `bin/simple compile test/01_unit/std/no_paren_test.spl`
   rc=1 (`struct 'Array' field 'len'`) -> rc=0.

2. **Index into a bare `tuple` annotation.**
   `fn f() -> tuple:` lowers to `HirType::Tuple(vec![])`; indexing it raised
   `Cannot infer element type for index into 'empty tuple'` instead of
   degrading to ANY the way every other unknown receiver does.
   Proof: `bin/simple compile src/os/crypto/ml_dsa_ntt.spl` rc=1 -> rc=0.
   This is the cause behind all 5 crypto spec rows (`power2round_poly`,
   `kpke_keygen_params`).

3. **`.ok` / `.err` on a receiver whose type was erased to ANY.**
   `try_lower_result_projection` needs a typed `Result` receiver; when the
   producing call's return type was not propagated it bailed and the access
   became a hard error. A last-resort dynamic projection (payload ANY,
   discriminant checked at runtime, placed AFTER every field-resolution
   attempt so it cannot hijack a real `ok`/`err` field) removes the
   native-only divergence.
   Proof: `aop_spec`, `di_injection_spec`, `result_type_spec` wrappers no
   longer fail in HIR lowering.

## RESIDUAL — need a decision or deeper work (NOT papered over)

### R1. Interpreter-only constructs in native codegen (5 specs)
`test/01_unit/std/given_working_spec.spl`, `test/feature/usage/structs_spec.spl`
fail with `Unsupported feature: Context statements require interpreter mode.
Native codegen support is planned.` After fix (3),
`browser_engine/net/resource_loader_spec.spl` (18 functions),
`aop_spec` (1), `di_injection_spec` (2) and `exists_check_value_return_spec` (1)
advance to the sibling gate `cannot compile to standalone SMF: N function(s)
contain constructs that require the interpreter`.

This is a declared, planned native-codegen gap, not a bug in these specs. The
DECISION needed is at the runner level: a spec that legitimately requires the
interpreter must be routed to an interpreter-only coverage lane, not compiled.
Silently accepting a degraded run is exactly what PR #157 closed.

### R2. Cross-module class type erased to ANY (4 specs)
`cannot infer field type while lowering simple_abi_digest_is_zero_v1: struct
'ANY' field 'w0'` — `src/lib/nogc_sync_mut/composition/abi_digest.spl:25`
declares `value: SimpleAbiDigest256V1`, imported via
`use std.nogc_sync_mut.composition.provider_contract.{SimpleAbiDigest256V1}`.
The declared class type is not in the lowerer's type registry at that point, so
the parameter degrades to ANY and its real fields become unresolvable.
Affects `cli_extension_config_registry_spec`, `cli_extension_help_completion_spec`,
`cli_extension_namespace_spec`, `cli_option_route_spec`.

### R3. Same family, browser_engine (3 specs)
`struct 'BeLayoutBox' field 'is_anonymous'` (anonymous_block_spec),
`struct 'BeDomNode' field 'id'` (dom_query_spec),
`struct 'ANY' field 'line_boxes'` (ifc_linebox_spec). Named struct is known but
the field is not found in the registry — likely the same cross-module
registration gap as R2, but confirm before merging the two.

### R4. Chained paren-less call on an ANY receiver (1 spec)
`exists_check_spec.spl` advances past `Array.first` (fix 1) and now stops at
`struct 'ANY' field 'lower'` — `s.trim.lower`, where `.trim`'s dynamic
MethodCall has type ANY. Deliberately NOT fixed here: making every
unresolvable field on an ANY receiver a dynamic method call would also convert
R2/R3's real compile errors into silent runtime failures. Needs a decision on
whether ANY-receiver field access should be dynamic.

### R5. Class literal with undeclared fields (1 spec)
`classes_spec.spl:290-297` declares `class ValueHolder` inside an `it` block
with methods only, and constructs it as `ValueHolder { _value: 10 }`;
`self._value` then has no declared field. The interpreter accepts this. Design
question: does a class literal implicitly declare fields? Do not "fix" by
editing the spec until that is answered.

### R6. Optional arithmetic (1 spec)
`shared_pointers_spec.spl`: `cannot apply 'Add' to an optional value that has
not been unwrapped`. The diagnostic already names the documented idioms
(`x ?? default`, `x.unwrap()`, `if val v = x:`). Flow-sensitive narrowing is
explicitly NOT the answer —
`doc/05_design/language/type_system/flow_sensitive_narrowing_design.md` is
status PROPOSAL. Needs a source fix in the spec that does not weaken its
assertion.

### R7. llvm_backend arm32 / i686 (2 specs) — OVERLAP
The wrapper generator returns the original path for these, and a direct compile
fails with `Undefined("undefined identifier: panic")` — the class owned by
`fix/cov-wrapper-undefined-identifiers`. The suite's
`` `case KwMod:` is not a variant of the matched enum `` diagnostic did NOT
reproduce through this harness, and `case KwMod` has zero occurrences in
`.spl` source, so that arm is generated rather than written. Re-triage after
the sibling branch lands.

### R8. `Trait coherence errors` (1 spec) — NOT REPRODUCED
`trait_coherence_spec.spl` compiles cleanly (rc=0) through the plain wrapper.
The suite failure is on the wrapper of the **coverage-instrumented**
`simple_cov_...` copy, which this harness does not produce. Needs a repro that
includes coverage instrumentation before it can be triaged.
