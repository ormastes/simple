# Generic function bounds discarded by flat frontend transport

Status: SOURCE REPAIR AUTHORED; all execution UNRUN.

The canonical `_ParserDecls/fn_struct_decls.spl` parser consumes inline trait bounds but only records them in file dictionaries. `parse_fn_decl` stores only where rows in the declaration. `_FlatAstBridge/convert_nodes.spl` then constructs every ParserTypeParam with empty bounds. Consequently source constraints do not reach existing HirLowering.lower_type_param or the active HM bound admission owner.

Port limitation: generic extern binder transport is absent from this release base and remains unchanged. The ordinary function inline parameter loop is replaced with the reviewed bound-conversion helper; no extern ABI/binder work is imported.

Repair: keep inline trait rows in a declaration-local tuple returned by the existing type-parameter parser implementation; its compatibility wrapper retains the original API. Merge inline and where rows by declared binder index before parsing the body. Hardware bracket/candidate/limit lists retain their existing dictionary handling and are not reclassified as trait conjunctions. The bridge invokes the existing canonical type parser on each retained fragment after the enclosing parse, then the existing flat type conversion; it does not implement a parallel grammar. Structured Named arguments survive. Newly detected parse errors invalidate cold capture and reject warm restored modules.

Generic type defaults have no grammar in this canonical owner. has_default remains false; value-parameter defaults are unrelated and unchanged. Impl/struct generic transport is outside this function-only repair. Parameterized trait bounds remain structured; the reviewed HM owner currently rejects unsupported trait arguments precisely. This packet does not claim support for solving them.

Ported source tests call parse_full_frontend and actual HIR lowering without injected constraints. Parsed infer_module integration is excluded until the separate active HM dependency lands. These are authored acceptance oracles, not PASS evidence. No compiler, runtime or build execution was performed. Only the authorized isolated port branch is changed. Historical exhausted campaigns remain unchanged.

Parser fragment validation follows the existing post-parse interpolation mechanism: the enclosing lexer is idle, type arena entries append, and the next module resets parser state. Compiler/source identity must invalidate old flat caches whose inline rows were absent; no wire schema change is introduced.
