# Accessor consumer integration checkpoint

Date: 2026-11-14
Status: source implementation in progress; not runtime-qualified or public get/set support.

The preceding typed-plan/emitter checkpoint is `447dd66e4698e21a7b75794abcd2c4d39394ae56` on the accessor feature branch. This follow-up connects those primitives to original field consumers. It has not been merged to release.

## Implemented source paths

- Both field-expression lowering paths consult the same frozen source-span decision. Field assignment consults it after lowering the RHS, preserving existing evaluation order.
- Explicit unmatched decisions retain ordinary lowering. Missing, unsupported, repeated, or unconsumed selected decisions produce diagnostics rather than silently omitting advice.
- The driver publishes checked source/HIR snapshots, complete canonical helper keys, reserved generated symbol identities, one physical emission owner and matching declarations. Workers cannot invent helper identities.
- MIR carries explicit versioned compiler-private bindings. Graph reconstruction preserves them; ordinary execution weaving, debug tracing and XRay exclude the recorded generated functions.
- The LLVM path emits hidden definitions and typed hidden external declarations from explicit records, not from a naming convention or the C-export flag.
- With no field-aspect requests and no active plans, the driver retains the original lowering call path.

## Evidence and limits

The earlier generator baseline, owner transport and tokenizer checks remain valid within their recorded scopes; none was repeated. New freezer and coverage specifications are authored but **UNRUN**. No native build was launched for this checkpoint. Static transient-boundary gate passed 18 invariants after adding explicit accessor/private metadata roots, reconciling two existing mutable-reference builder roots and recognizing the existing public SFFI wrapper. Evidence: `/tmp/accessor-transient-inventory-20261114-run2.log`. The initial run exposed those inventory/scanner drifts. This is static evidence, not compiler or native behavior qualification.

Actual selector-to-provider plan production is still missing. Public get/set remains rejected by E1507. Imported receiver relocation currently requires exact physical identity and fails rather than inventing a compatible representation. Publication now requires the canonical driver target context to admit LLVM Linux; auto backend requests and flat/captured transport are rejected. Object/cache serialization still needs a complete preservation/identity policy before plans can be enabled. The immutable source snapshots and metadata must also enter final object/cache identity.

The initial integer/bool reference-class profile is a staged implementation slice. Managed references, value aggregates, RMW, atomic places, broader target support, optimizer qualification, original permission provenance, complete P0 tooling/catalog parity and full integration evidence remain obligations. No assertion here qualifies those paths.
