# Pure-Simple if-val Boolean payload provenance

Status: source-confirmed missing typed lowering; candidate repair, native validation UNRUN.
Source pin: 4da06603013a468071da66824a933051a4c10b07.

The flat parser marks synthetic if/elif/while-val declarations. FlatAstBridge converts the marker to ExistsCheck so presence remains distinct from payload use. ExistsCheck MIR preserves a raw i64/nil-sentinel result until the guard; only Float payload provenance was registered. lower_if and lower_if_chain similarly rebound only Float in the present arm, and enum_payload_value lacked a Bool case.

That gap permits a RuntimeValue-backed false payload (19) to remain a nonzero integer in a bound value condition. This is related to the Rust seed optional-Bool bug, but the representation boundary differs: pure ensure_option_handle passes raw Boolean0/1 to rt_enum_new, while RuntimeValue Boolean is19/11. Calling rt_value_as_bool blindly would reject rawtrue1. The candidate preserves Bool semantic provenance, rebinds a typed scalar only in selected if/elif arms, and decodes the two legitimate true representations (1 and11). rt_is_some and ordinary optional presence semantics are unchanged. No schema or serialized enum changes.

The eleven-case native fixture exercises native and RuntimeValue-backed producers, false/true/absent, elif, and ordinary presence. It must be compiled and executed by refreshed self-hosted LLVM and Cranelift producers. It has NOT been run and is not admission evidence. The Rust seed seven-case fixture remains independently owned.

## Separate while-val repair candidate

The original while-val form used a nil-break guard followed by the body, outside the present-arm typed payload boundary. The follow-up changes only identifier-form parser desugaring to a marked binding plus `if NAME != nil: BODY else: break` inside the existing unconditional loop. The initializer is still evaluated once per loop test, and break/continue/return retain their surrounding loop/function targets. The selected arm reuses the existing float/Boolean MIR binding and restores the raw binding afterward. Constructor-pattern loops remain on their existing match route.

The separate ten-case native fixture covers raw and tagged false→true→nil streams, initial absence, break, continue, return, outer-name shadowing, exact initializer-call count (including the terminating nil test), and the float path. Both fixtures remain UNRUN; source review and parser/source-bound cache invalidation are required before a refreshed producer can establish native correctness. No flat AST wire fields/tags changed; parser-source identity must invalidate cached old desugarings through the existing authority owner, never forced cache reuse.

Explicit optional access followed by manual nil guards shares the existing Float mechanism; broad optional ABI redesign is outside this repair.
