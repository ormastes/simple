# Configured library variants and aggregate validation

Use this guide when changing library imports, compiler generations, or array/tuple behavior. It records the original design and the evidence needed to validate a repair; it does not declare the active Rust/Pure-Simple parity work complete.

## Preserve the selected configuration

The original design exposes stable interfaces while configuration selects their implementation. GC/no-GC and sync/async families are implementation choices, not interchangeable spellings. Preserve explicit configured selection and the importing module's family when resolving generic library names. An explicit family-qualified import selects that physical owner deliberately; document it when a boundary requires it.

Candidate fallback order is a search mechanism. It must not silently override a configured choice or choose a different owner during source discovery, frozen export resolution, or HIR lowering. Missing support should produce an attributable diagnostic. Do not fix a generic import by globally pinning GC, no-GC, sync, or async. A real missing leaf import can be repaired at its declared owner without changing global selection policy.

Compare the Rust bootstrap resolver and the Pure-Simple pipeline using the same requested configuration, importer, source inventory, and module spelling. Check the selected physical module and export owner at each stage. A source patch to discovery alone does not prove that HIR selects the same owner. Configured-selection parity is active work; historical fixed candidate ordering is not proof of the intended contract.

## Bind observations to the compiler that produced them

Record source revision, producer executable hash, runtime/provider identity, backend, relevant options, and actual cache scope. A repaired source tree compiled by an older producer may repeat an already understood grammar or resolution failure. Mark that result pending a rebuilt producer rather than repeatedly editing the leaf or claiming it passed.

Preserve previous failure evidence and successful cached objects. Let canonical producer/source/runtime/option identities invalidate caches naturally. Do not force a cache key, mix backend proofs, or treat an archive declaration as evidence of the provider linked into the executable.

## Validate aggregate semantics, not only shapes

For arrays, tuples, destructuring, generic returns, and Result/Option payloads, require actual values as well as lengths. Cover empty/single/multiple elements, byte values including zero and non-ASCII octets, cross-module constructors and reads, copy/mutation behavior, and owner lifetime where relevant. Use real positive and negative contracts; unresolved associated types or duplicate record fields are separate source defects, not permission to erase language features.

Run the smallest meaningful regression through the interpreter and both actual Pure-Simple native backends. Compare fresh and warm cache behavior where cache changes are involved. Bind runtime ABI observations to the actual linked provider/layout. Parser-only acceptance, module inventory size, and number of object files do not establish aggregate correctness.

Query each produced test binary's real registered inventory before execution where the existing runner supports it. Retain pass/fail/skip counts and zero-case guards. Do not replace those counts with source-file counts or introduce an external test framework.

## Current evidence boundaries

The retained frozen147 Phase3 ledgers reported four aggregate-type diagnostics for `hash.spl` under an older Phase2 producer. Composite-impl source repairs and subsequent producer builds are distinct evidence; neither is a universal Hash or array/tuple PASS. Likewise, a nil/invalid policy text length is not proof of positive size overflow or a shifted tuple payload. Track the first observed failing boundary before choosing a fix.

The authored robust array/tuple plan has not yet been identified. Existing research options and older fixed-array/extern-return plans must not be presented as that selected plan. Broad structural changes require that exact authored scope; confirmed narrow regressions can still be repaired independently.

Related maintained references:

- [Native test binary workflow](../infra/testing/native_test_binary_workflow.md)
- [Syntax quick reference](../quick_reference/syntax_quick_reference.md)
- [Host CPU runtime variants](../../04_architecture/runtime/host_cpu_runtime_variants.md) — a separate configured runtime-tier contract, not a substitute for GC/concurrency-family selection.
