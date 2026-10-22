# Imported inline constants must not acquire consumer storage

Independent review of integrated `857fc79a382` found that the address guard added
by `23833413eac` trusted consumer `HirSymbol.visibility.is_private()`. HIR import
registration makes imported symbols Public, even when the provider declaration is
a private immutable literal with no storage. The guard could therefore create a
public consumer data definition under the provider's name; two consumers could
produce duplicate definitions and different addresses.

## Authoritative origin and call-path audit

Use existing `global_const_exprs` membership to authorize materialization after
finding the folded value. This map is local-declaration provenance, not imported
symbol visibility. Its only writer is `lower_const` in `function_lowering.spl`,
which unconditionally records the local initializer (including Unit's deliberate
placeholder) before writing the corresponding `global_constants_by_id` value.
The only other writer of folded global values is `register_provider_globals`,
whose private-inline branch records the exact value on each demanded relocated
consumer SymbolId, but deliberately never imports provider HIR expressions.
Import aliases therefore preserve the same distinction. Both existing maps use
the consumer namespace; this change adds no new SymbolId remapping assumption.

The address materializer has one caller, `try_lower_global_addr`. That caller
first resolves lexical locals, then uses existing static storage if present,
and only otherwise requests folded-value materialization. Public or mutable
imports retain their external MirStatic and initialization path. Local private
constants retain local initializer provenance and may acquire local storage.
Imported inline values have neither local initializer provenance nor a static,
so address-taking now reports the existing error before a definition is added.
Ordinary imported constant reads and provider initialization bookkeeping do not
change.

Both maps already initialize in the canonical MirLowering constructor, reset
together at module lowering, propagate together to lifted-lambda lowering, and
participate in transient-owner root promotion. No extra map, traversal, clone or
lambda propagation is introduced. The change replaces symbol/visibility/owner
lookups and text canonicalization with one existing dictionary membership check
on the uncommon materialization path. Runtime performance remains unmeasured.

## Regression scope and evidence

The unit spec models provider-import provenance with a Public consumer symbol;
materialization must return nil, report an error, and add no static. A local
private constant control must still materialize successfully.

The existing native global-storage fixture now checks mutable address identity
between provider and two consumers, public immutable identity between consumers,
local and provider-private address stability, shared mutations, and initialization
count one. The private-address negative has two consumers of the same inline
literal; the second uses an import alias inside a lifted lambda. Both must reject
address-taking, with no linked binary or consumer definition for INLINE_LABEL.
An eventual ELF check must show one definition each for VALUE and PUBLIC_NUMBER
and none for the imported inline label. Run on both LLVM and Cranelift with the
same sources and the compiler/runtime authority containing this repair.

Source review and whitespace validation only. Unit/native execution is pending
the coordinated producer; no build was launched during the disk hold. Existing
historical accessor-helper evidence does not qualify this ownership fix.

## Follow-up: retain diagnostics from first-class lifted lambdas

The second independent review found that `lower_lambda_value` lowered a lambda
body in a fresh MirLowering but discarded its errors and advisories before
publishing the function. The address guard correctly called `error_fatal` on
that child, yet unary lowering could continue with a temporary reference. An
escaped lambda therefore lost the required compile rejection. The original
direct negative masked this path, and a directly called lambda may beta-inline.

Transfer the child's original MirError records and advisories to the parent
immediately after body lowering. Preserve messages, spans and fatal flags;
warning-only diagnostics retain their existing driver classification. An explicit
child fatal now returns nil before end_function or publication of lifted MIR and
statics. Nested lifted failures propagate through the same boundary. Transfer
visits only child diagnostics; no new global map traversal or lowering-state copy
is introduced. Performance remains unmeasured.

The standalone `private_address_returned_lambda.spl` negative returns a lambda
and passes it to another function; its only illegal address is inside the lifted
body. It must fail compilation with the imported-inline ownership diagnostic and
must not produce a binary. Diagnostic unit cases check fatal propagation, source
span/advisory retention, and warning-only behavior without deleting parent errors.
These regressions are authored, not executed during the disk hold.
