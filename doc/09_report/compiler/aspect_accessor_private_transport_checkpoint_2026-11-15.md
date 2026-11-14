# Accessor private transport checkpoint — 2026-11-15

Status: source implementation; new executable specs UNRUN. This does not enable public `get`/`set` selectors or qualify native generated accessors.

Base: the eight accessor feature commits were rebased onto release `ce5b5d9759ca4d6b2c7e59e69ec6de65342139ca`, producing reviewed feature head `712cd13979c77a77a77974fc3a1206f5c1df8560`. Seven patches were identical; the consumer patch dropped a transient-scanner hunk already present upstream, retaining upstream's stronger public-function termination check. No HIR schema or generated codec was changed by this checkpoint.

## Implemented source changes

`mir_compiler_private_encoding_v1.spl` emits a canonical, sorted explicit JSON record for the existing MIR interchange surface. It includes schema, publishing module, each physical symbol, final linkage name, emission owner, complete canonical key and index digest, definition/reference status, and every current `MirSignature` field, including declared parameter facts and coercion provenance, recursively through composite types and nested function-pointer signatures. The old generic signature JSON omits some of these facts, so it is insufficient for this metadata.

Both native capsule identity implementations and the canonical MIR fingerprint include this record. The historical MIR report serializer exposes it. Empty legacy modules append nothing and preserve their existing bytes. This is encoding and identity integration, not an executable MIR decoder or a claim that every historical transport understands private helpers.

The actual source producer runs before prelower cache lookup. Prelower witnesses and file-worker reuse rows do not yet bind complete accessor plans; field-aspect builds now bypass those two early reuse optimizations and consume their real plans. Ordinary builds retain the existing paths. The post-MIR object cache continues to use the current complete capsule identity.

Bootstrap skip-MIR and whole-program flat lowering now reject requested field plans, rather than returning empty/unmodified MIR. Plan publication admits only the current explicit native route; SMF, combined, self-contained and runtime-std transport remain unavailable. The actual SMF object-spool producer and runtime-std MIR payload owner also reject nonempty private metadata before encoding/publishing it, including a retained publishing identity without records.

## Evidence and limits

Static hygiene: working and staged direct-env guards PASS; staged whitespace check PASS. The sparse checkout does not materialize `doc/06_spec`; the complete tracked-file index reports zero executable `*_spec.spl` files under that path. These are source hygiene checks, not executable test evidence.

The private identity specification covers empty legacy bytes, reordered metadata, same-index/different-full-key changes, independent linkage/schema/owner/definition mutations, declared ABI/coercion changes, and runtime-std transport refusal. It is authored but UNRUN. No new compiler, parser, backend, or native execution is claimed. Existing scanner, owner-transport, generator and static transient-inventory evidence remains scoped to its original checks; none was rerun to manufacture a new pass.

The early reuse restrictions are staged admission limits, not final feature requirements. Full support needs versioned witnesses carrying complete plan/dependency identity and a validated private-linkage transport. Public `get`/`set` remains rejected until actual source-to-binary qualification; managed/reference field values, generic instantiations, value places, RMW/atomic/borrow cases, attributes/export-boundary facts, complete tooling parity and imported-provider qualification remain obligations.

## Smallest next native qualification

Use a self-hosted candidate containing the actual accessor frontend, provider, MIR consumers, hidden linkage and this transport patch. The previously admitted producer cannot exercise new compiler logic merely by compiling manually built MIR helpers. Pin candidate/source/runtime hashes, target and private cache. Request a finite resource budget before launching; no build was launched for this checkpoint.

First run the existing `test/02_integration/compiler/aop/fixtures/accessor_scalar` source fixture through an internal qualification candidate on the admitted LLVM Linux/no-GC profile. Assert RHS-before-receiver and evaluation once, one actual read/store, getter result retained through alias mutation in after-success advice, committed setter semantics, and allocating advice. Add a real two-module imported receiver/alias case and inspect hidden definition/declaration/call identity. Exercise warm post-MIR reuse after changing only advice body/owner and require the affected object to miss. Compare no-aspect compilation with the same candidate. Add active transient-scope churn while the owner remains alive, without dereferencing after explicit scope teardown. Public admission must remain closed if any oracle or necessary compiler route is unavailable.
