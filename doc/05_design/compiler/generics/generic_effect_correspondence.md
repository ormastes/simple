# Generic effect substitution: production correspondence boundary

Date: 2026-10-19. Status: source implementation and executable oracles authored;
compilation, SSpec execution and production refinement are **UNRUN / UNPROVEN**.

## Requirement and actual gap

This implements part of approved G2 in
`doc/03_plan/generic_formal_verification_hardening_plan.md`: recursive
substitution must include type-bearing effects. On release base
`e74e7f6529e5d559c72cc32a578af4d54ce7351b`, `substitute_type` substituted
function parameters and return type but retained `Throws(T)` unchanged.
`substitute_function` and `canonicalize_template` also omitted declaration
effects. `EffectKind.Throws` owns a `HirType`, so these omissions retain an
unbound type in an otherwise specialized signature.

The production correction reuses the independently reviewed
`generics-throws-20261016/production.patch`. One shared `substitute_effects`
walk changes only Throws payloads, recursively using `substitute_type`.
All other effect kinds, order, spans and absent-versus-empty representation
are retained. The three APIs call the same walk. Existing symbol-keyed
canonicalization still binds only the declaration's actual type parameters.
The eight actual API scenarios from that packet are retained unchanged.

The earlier `generic_subst_model_refinement_spec.spl` has a deliberately
bounded universe: its function projection takes only the first parameter
and excludes effects. Its results cannot witness this obligation. The new
bridge is separate; no previous finite result is retroactively widened.

## Structural projection contract

`src/compiler/40.mono/model/generic_effect_projection.spl` maps a declared
HIR fragment to the existing `MType` algebra, returning `Err` outside it.

| HIR data | Model representation |
|---|---|
| Unbounded TypeParam | Var with the exact parameter name |
| Int / Float | Distinct constructor plus exact width and signedness |
| Bool, Char, Str, Unit, Never | Distinct scalar constants |
| Tuple / Optional | Tagged application with all recursively projected children |
| Function | Function(Params(all parameters), return, Effects(all effects)) |
| Throws(payload) | Effect.Throws(project(payload)) |
| Pure, IO, Async, Mutates, Allocates | Separate effect constants |
| Custom(name) | Effect.Custom with a literal prefixed name child |

Lists retain order and arity, including zero parameters. Reserved constructor
tags are distinct across type/effect categories; Custom names are literal
children, never variables or constructor tags. The prefix also prevents a
custom name `?` from becoming the model's unknown sentinel.

Absent types, bounds, parameter/effect lists and effect nodes refuse. Bounded
parameters, nominal symbols, arrays and all other forms outside the table
refuse, including Any and Error. No unknown-success fallback is allowed.
Nominal identity needs an owner witness and is deliberately unsupported here.
An unsupported child, including inside Throws, rejects the entire projection.

Spans are outside this semantic quotient. Their preservation, input
immutability, symbol binder ownership and absent effect list behavior are
separately asserted by `generic_effect_substitution_spec.spl`. The bridge
does not establish equality of complete HIR records.

## Executable correspondence and proof boundary

The new SSpec compares, using structural equality:

`project(substitute_type(h, S)) == ms_apply(project(S), project(h))`

Its exercised name-keyed substitution is T to a represented integer, with
explicit unbound Outer controls. Symbol-keyed normalization is checked by
the separate actual API spec, not silently included in this equation.
Expected terms are constructed from the original input and replacement;
they are not copied from the actual result. A negative control reconstructs
the old output with concrete parameters/return and stale Throws(T), and
must be rejected. Other controls detect parameter truncation, effect
reordering, scalar erasure and unsupported-input false agreement.

`GenericSubstModel.lean` already models arbitrary application constructors
and recursive substitution. Its existing `apply_compose`,
`apply_idempotent` (closed-range premise) and `apply_supported_closed`
theorems remain unchanged and model-only. Using new constructor labels
does not require changing the algebra or theorem text. Neither a checked
HIR projection theorem nor executable Simple-to-Lean correspondence is
claimed. The authored finite API checks must still be executed on an
admitted runtime; the eight prior model builds are not rerun or counted as
production verification.

Archive signature/caller effect propagation, effect parameters, all-HIR
coverage, end-to-end compiler behavior and full G2/G1–G7 acceptance remain
separate obligations. This change creates no receipt/signature authority,
release admission, cache policy or build retry authorization.
