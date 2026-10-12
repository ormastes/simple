# Generic call linkage from actual template metadata

The prior metadata regression referenced `global_linkage`, but the actual
MonoTemplateSignatureV1 and call rewriting did not implement it. Free-call
rewriting used the original caller spelling (`mono_requalify`); generic method
rewriting always qualified foreign specializations. A bare or aliased imported
ordinary call could therefore name a different symbol from the actual emitted
provider, while global ABI declarations must keep their unqualified linkage.

The body-free signature now projects the real declaration's extern/export/
global/entry attributes, preserves the flag through specialized signatures,
and binds it into signature digest domain v2. One shared rewrite owner stamps
both free and generic method callees: global ABI or same-module calls remain
bare; other calls use the actual registered template module. Existing function
attributes, extern ABI, generated-body placement and nominal signature
transport remain unchanged. Original display spelling is not authority.

The source-bound metadata spec now contains five `it` groups. Its complete
parsed/lowered generic declarations exercise both retained and archive request
modes, generated-body/request owner and actual rewritten call bodies, a
misleading display-qualifier fault input with the real resolved symbol, and
actual generic impl receiver transport. The global-attribute controls explicitly
modify those metadata fields on parsed declarations; they are mechanical
controls, not evidence of final compiler admission. No synthetic tiny HirModule
or manually fabricated signature replaces the actual source bodies.

All five groups are **UNRUN**. Whitespace/source review does not qualify the
Simple producer, generic calls at native link/execution, or the archived route.
