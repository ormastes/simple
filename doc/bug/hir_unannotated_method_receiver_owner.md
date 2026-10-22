# HIR-RECEIVER-OWNER — primitive method receiver inference transport

Status: source repair and six actual API scenarios authored; all execution UNRUN. No exhausted campaign is restarted.

The active parser synthesizes self with type tag zero for lowercase primitive impl targets. The flat bridge correctly marks this parameter unannotated. HIR lower_impl has already resolved the enclosing text target to Str, but lower_function skips its synthetic receiver path because self exists. lower_param then lowers the absent receiver type to Infer. Retained final attempt3 HIR has function113 to_internal_text parameter308 self Infer(0,0); function117 on ExternalText has Named78. This proves signature transport failure before body Result/Try processing.

The repair passes the enclosing owner only for the first unannotated self/me of a nonstatic method. Explicit annotations and other parameters retain existing behavior. Unresolved supplied owners fail closed; no Any/integer coercion. Generic owner values are transported unchanged, not reconstructed by spelling.

Landing scope: this standalone compiler repair does not include the separate external_text foundation or its temporary explicit-self consumer bridge. The explicit receiver regression remains as a grammar and ABI preservation control. Historical cache evidence comes from that external qualification campaign; no test or runtime PASS is inferred here.

Validation: spec uses parse_full_frontend and actual HirLowering, checking primitive/named identity, annotation precedence, ordinary/static controls and unresolved owner refusal. Runtime/native/alias/generic specialization qualification remain pending. No binary was executed. The precursor packet has independent source/API/oracle approval; this release-base port requires its own review.
