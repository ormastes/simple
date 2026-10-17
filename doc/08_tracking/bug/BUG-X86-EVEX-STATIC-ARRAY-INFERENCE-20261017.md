# BUG-X86-EVEX-STATIC-ARRAY-INFERENCE-20261017

Date: 2026-10-17. Status: open compiler inference bug; source workaround drafted.
Authoritative DB reconciliation pending; no qualified DB tool is available.

Immutable producer: 0015c3fe0dfd28c22e55cbe488636f30e5baa869d1608cad4847685b9c553429.
Original source: 15f7ca45871b1250abf44c91efb6004625035035.
Recovery reference: actual tiny-source commit c6e8c8a43b64670c96d244aab7a14ad7c8661131.

Focused cycle two admitted a genuine co-located source snapshot, then MIR
reported unresolved module-static initializer types at
`src/compiler/70.backend/backend/native/_X8664Avx512/evex_encoding.spl:82:27`
and `:110:25`. The arrays are X86_ZMM_ALLOCATABLE (register IDs 48..79) and
X86_K_ALLOCATABLE (81..87). Their constants are integral register IDs and
downstream helpers use i64 register operands. Explicit `[i64]` array annotations
retain every element and its order and avoid the producer's inference failure.

Both temporary annotations have immediately preceding canonical workaround
tags. The intended recovery is removal of annotations only after the inference
owner accepts the original unannotated declarations under the same focused
regression. These annotations do not fix the compiler inference owner.
Actual diagnostic workaround commit:
07f13d853d0f917593aff3673ae27712a3240ed1 in the genuine owned co-located probe
repository. The separately reviewed production source change remains a draft.

Evidence: co-located-cycle2/compile.log and resource-guard.receipt in the parent
evidence directory. MIR: 64 modules, 62 succeeded, two failed modules (this
module plus the independent parse_i32 defect). Exit 1; objects 0; no executable.
Background owner: compiler MIR module-static type inference.

Focused cycle three passed MIR65/65 and emitted54 new AMD64 COFF objects,
clearing the original inference failures with both annotations present.
Compiler exit was1 during runtime discovery because the tiny source checkout
has no src/runtime; --runtime-path supplies runtime artifacts, not C sources.
This is codegen evidence, not native behavior or broad core qualification.
