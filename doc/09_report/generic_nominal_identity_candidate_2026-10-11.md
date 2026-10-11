# Generic nominal identity candidate

STATUS: WARN — source candidate; executable verification pending.

Staged whitespace, numbered-artifact and direct-runtime-facade guards passed.
Independent source review found a repeated-type-parameter alias equality gap;
the shared owner-key encoder and alias regressions address that finding. This
is source evidence only, not execution verification.

This is a separate change after H-ANNOT commit `9514acf4b70`, on
`work/rel-generic-annotation-preservation-20261011` in
`C:/dev/simple-rel-generic-annotations`. No release admission is claimed.

`MonomorphizationPass.type_key` now resolves each nominal leaf in the current
module's actual symbol table, then encodes canonical declaration owner and name
with component lengths. All recursive constructors retain that identity.
The shared encoder lives in `40.mono/nominal_type_identity.spl`; repeated type
parameter witnesses use the same encoder in the caller's table, so two import
aliases of the same declaration no longer conflict merely because ids differ.
Unknown ownership propagates an empty key; `mangled_name` records E-MONO-041 and
`request_specialization` returns -1 without registering a symbol. Inference uses
`same_type_key` so two empty keys do not establish equality.

Display names retain the existing mangling and `_k<n>` suffix. Constructor
inference uses the caller table's imported symbol rather than returning a
foreign declaration id from the global short-name table. Context-bearing
binding also checks argumentless nominal patterns, while production callers
refuse nominal evidence when their table context is missing. The explicitly
context-free model API remains a single-table operation.

Tests prepared, not run:

- Owner-key tests: colliding ids and names, shared declaration across distinct
  ids, nested arrays/function returns, suffix stability, missing-owner rejection,
  and rejection of a value-symbol id masquerading as a nominal type.
- Two fixed-nominal cases in the annotation-owner binding spec.
- Repeated type-parameter witnesses through distinct import aliases, including
  a nested array witness, using canonical caller-side ownership.
- Existing bounded differential now registers its model nominal ids as real
  declarations. It still checks equality/injectivity, not exact model/production
  key byte equality or proof of refinement.
- Two-module native fixture: identical short type names/layouts, two expected
  LLVM specializations, and exact stdout. Stdout alone cannot prove key separation.

No admitted self-hosted test runtime is available to this lane. The current
diagnostic successor does not contain the candidate. No test count, coverage,
native pass, or formal refinement proof is claimed.

Remaining adjacent risk: caller-local nominal ids currently enter a specialized
body placed in the template module, and provider-local return/parameter ids are
copied back into caller stamps. This source ownership transport needs the
separate HIR relocation repair before claiming complete H-XMOD or H-RET32.
