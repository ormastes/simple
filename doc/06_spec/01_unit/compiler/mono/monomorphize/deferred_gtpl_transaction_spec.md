# Deferred GTPL transaction — manual evidence

Requirement: REQ-GENERIC-GTPL-TRANSACTION.
Executable owner: test/01_unit/compiler/mono/monomorphize/deferred_gtpl_transaction_spec.spl.
Six cases UNRUN; this manual is authored, not generated from passing execution.

1. Serialize actual FunctionDef records using serialize_templates, then call
   deserialize_templates. Check decoded generic/parameter/return/body fields,
   final duplicate replacement, unrelated old rows, and cleared prior error.
2. Increase a valid one-record section count to two. Require false at missing
   record1 with the exact EOF error and the original cached definition intact.
3. Truncate the final byte of a real two-record section. Require false, a real
   decoder error, no first-record publication, and no earlier-cache loss.
4. Replace the second kind byte with99 at the canonical first-record boundary.
   Require the actual decoder's Unknown template kind error and no publication.
5. Load a canonical zero-count section successfully, then test missing record0
   and extra trailing bytes. Preserve the original cache through both failures.
6. Refuse version3 before mutation, then load a valid section successfully with
   error cleared and all old unrelated rows retained.

No replacement decoder, runtime body compilation, CLI loader qualification,
performance PASS, gate enablement or workaround retirement is claimed.
