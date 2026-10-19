# Class-owned static specialization draft

Status: PREPARED, all compiler/native regressions UNRUN. Base:
`3ca2b121b8a85e1a0eaa79157f9a40d11492ee7f` (`release_phase3`).
Canonical bug: `native_future_receiver_typeparam_2026_10_18`; its shared
dated evidence report is owned in the separate caller-repair lane. This
draft does not alter that lane, frozen authority source 97d8, producer 3c6,
or either immutable shared runtime-probe source.

## Why this transport change is necessary

The actual authority run attributed six unsubstituted T errors to two modules.
The subsequent real-Future baseline and explicit-receiver control both failed
with six T diagnostics, MIR 52 total / 51 successful / one failed and no
objects. The explicit control is negative evidence, not a successful caller
workaround. Its guard completed nonzero and quiescent; production-owner tests
were not run after the failed control.

Source inspection identifies two independent losses. First, both flat-parser
postfix paths consume `Future<bool>` but retain its arguments only if the next
token is `(`. A following dot loses the explicit owner arguments. Second,
class lowering flags a method as a generic template but leaves class-owned T
outside the method's own generic parameter list. Mono's ordinary function
collector therefore does not register that class static as a template.

## Narrow implementation

- Preserve explicit owner arguments on the receiver's existing flat
  `expr_call_type_args` side table. Clone/flat serialization already includes
  this per-expression table; no new format or schema is introduced.
- Decode those arguments onto the existing rich receiver `Expr` metadata.
  The HIR method-receiver helper binds them only to a resolved nominal type
  owner and stamps `Named(owner_symbol, arguments)`. Both method-lowering
  paths consume that helper; value receivers keep their existing route.
- Register static methods of generic classes, when the method has no own
  generic parameters, with `MonoTemplateRecipeV1` over the class parameters.
  Reuse existing archive signatures, recipe materialization and worklist.
  `generic_methods` uses a distinct `static::owner-identity::method` key, so
  instance dispatch cannot accidentally prepend a receiver to these calls.
- Share existing call inference/specialization through
  `rewrite_template_call_v1`; select the class recipe by exact nominal owner
  and pass explicit owner arguments before ordinary argument inference.
  Existing nominal relocation, conflict checks, result signature stamping and
  exact specialized callable symbols remain in charge. No self argument is
  added. The MIR TypeParam rejection is unchanged.

This draft does not broaden `rewrite_expr_with_context`, implement implicit
context-only pending inference, reinterpret method-level `pending<bool>()`
syntax, or combine class-owned and method-owned type parameter scopes. Those
cases keep their existing paths. `Future<bool>.pending()` carries explicit
class evidence; an untyped `Future.pending()` is expected to fail inference.
Mixed owner/method generic scopes need a separate scoped binding design before
changing their route. No caller is allowed to guess a type from its name.

## Review and verification boundary

`test/01_unit/compiler/mono/mono_class_static_owner_spec.spl` lowers actual
source, rather than fabricating HIR call nodes. It covers inferred bool,
explicit pending owner arguments, missing/conflicting type evidence, retained
and archive recipe registration, and an imported nominal payload. It compares
the caller's symbol with the generated function and requires one argument for
from_value / zero for pending, concrete signatures and no residual type args.
The small class fixture isolates class-owned generic binding; the separate
real production-Future fixtures remain necessary native qualification.

Existing `mono_static_generic_factory_spec.spl`,
`mono_static_generic_call_contract_spec.spl` and
`generic_class_impl_template_lowering_spec.spl` are relevant regression
controls for method-owned generics, ordinary static calls and non-emittable
class templates. None has been executed for this draft. Parser owner-metadata
roundtrip and archive materialization/native execution still require explicit
verification in the reviewed plan; archive registration alone is not that
proof. No producer rebuild, native extra job or release qualification is
claimed or authorized by this draft.
