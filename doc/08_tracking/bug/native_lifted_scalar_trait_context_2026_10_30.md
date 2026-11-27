# Full-HIR lifted closures lose registered trait dispatch authority

Status: reproduced with admitted compiler14; minimal source repair prepared, native validation pending.

The unchanged `test/fixtures/compiler/scalar_trait_call_receiver/nested.spl`
(SHA256 `18d80877b06605067de10bd9e5af99199173d45493aef6821628540e4ee97fdd`)
fails native compilation with compiler
`6be3bc0edb4adba4b23d90d9b12e180515ff65fc39a6031423a432c4bbe37dfb`,
source `249e4d01e795753d33fc0357566cdf3fccee7f1c`, runtime snapshot
`6f77c096a705c609fd4e217daace99b5aec15330b3a798a9216c281cc94483a6`.
Evidence is `/tmp/attempt14-focused-nested-24g-20261030`: compile exit1,
selected SCV audit PASS (15152 inputs), no executable. The retained log reports
`unresolved method call: measured` at lines9,14,23 and consequent lambda
materialization errors. The ordinary receiver call does not report that error.

Compiler14 propagates the admitted return-type interface into a fresh lifted
lowering, but copies `trait_impl_owners`, `trait_impl_methods` and
`trait_impl_closure_complete` only when a declaration repository exists.
Full-HIR modules register these same carriers before body lowering. Scalar
fallback dispatch requires their exact receiver/method key, ambiguity marker
and complete implementation closure; an inherited RTI alone cannot supply it.

Move only those three read-only dispatch carriers beside unconditional RTI
propagation. Both lowering lanes retain identical admitted trait metadata.
This change does not copy child locals, builder, errors or inference scratch;
no guessed target, relaxed ambiguity check or runtime-panic fallback is added.
Declaration-specific metadata remains under its existing gate.

Retain the original nested fixture unchanged: it covers direct/lifted/nested
receivers, exactly-once effects and same-leaf i64/bool callable aliases. Add
`lifted_ambiguous_negative.spl` requiring the exact ambiguity diagnostic at
compile time, plus retain existing missing-lifted/missing-nested negatives.
The real unchanged SSpec green and assertion-red must also execute after the
new producer is built. Full-HIR and declaration-backed native routes are
separate coverage criteria. Source inspection is not runtime qualification.

## Independent review: preserve devirtualization evidence

Inheriting trait owner tables also permits full-HIR lifted trait-object calls
to devirtualize. Seed and adopt the cumulative `devirtualized_calls` counter
outside the repository gate, so successful sibling/nested lifts contribute to
the parent's independent E-MONO-038 archive verifier. Errored lifts already
abort before adoption. The driver separately forbids archive-producing lanes
from devirtualizing; no actual archive bypass was reproduced.

The existing real parse/HIR/MIR test owner `trait_typed_receiver_dispatch_spec.spl`
now lowers two sibling trait-parameter lambdas, requires two actual `Mem.list`
calls and a counter delta of two, then checks archive rejection using that
measured delta. This regression is authored, not executed; no fabricated count
is used as proof of propagation.
