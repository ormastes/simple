# HIR resolved reference snapshot v1

REQ-MC-008 prerequisite evidence. Runtime and performance: **UNRUN**. This
authored manual mirrors `test/01_unit/compiler/hir/hir_reference_snapshot_v1_spec.spl`;
it is not generated execution evidence and admits no rename or redirect.

The spec calls the checked production frontend, frozen module surfaces, explicit
semantic lowerer and real HIR collector. Missing implementations fail visibly.

| Scenario | Required observation |
| --- | --- |
| Deep real HIR | 192 nested unary expressions retain one real call and a node count linear in actual fixture depth, without an implementation depth ceiling. |
| Wide real HIR | 128 scalar local statements plus a final call produce 129 call facts, bounded linear node visits, and capacity failure only for an exhausted explicit node budget. |
| Local and recursive calls | Declaration and two calls share the actual local SymbolId and declaration origin. |
| Parameter and block shadows | Distinct value bindings produce no target function facts; comments and strings add none. |
| Unicode and lexer ownership | Original codepoint 7 maps to UTF8 byte 8; the owned map survives a second file's parse. |
| Import alias | Actual frozen terminal is pkg.one ordinal 0; source, alias declaration and alias use retain distinct roles. |
| Unsupported loop | Whole module returns unsupported_syntax. |
| Consumed frontend metadata | Actual representation-boundary decorator source is refused even if a composed frontend stores it outside ParserFunction.attributes. |
| Multiple import boundaries | Both list delimiters, multiple items, Unicode, comments and repeated target spellings retain exact original byte slices and separate terminal origins. |
| Unsupported/malformed imports | No complete fact set is returned. |
| Wildcard parser exits | Both actual parser exits retain the exact consumed star boundary, including EOF. Wildcards remain unsupported for collection. |
| Candidate capture | Independently resolved candidate refuses a call captured by a scalar parameter. |
| Node/reference budget | Each exhausted budget returns capacity, never partial success. |
| Sequential requests | Valid, invalid, valid requests expose no stale parser failure or accepted recovered module. |

Run only through the qualified self-hosted engine when root authorizes execution.

The request-wide terminal declaration index is prepared once; per-module
collection reuses it and resets only module scratch. Test additions after the
frozen initial receipt strengthen provenance coverage and track the authorized
`prepare_declarations` API amendment; they do not replace positive HIR assertions.

The collector owns the current source index and symbol-table reference once per
module. Borrowed helper methods receive scalar IDs or plain token/declaration
records; neither dictionary owner crosses a per-reference call. The module
collection API omits the already-prepared request-wide declaration inventory.

Cycle 2 retains each concrete parsed module in a fixture-owned array, assigns
its explicit configured module name before surface construction, and passes the
concrete array entry to HIR lowering. A nullable dictionary lookup never crosses
the lowerer entry boundary. All cases remain UNRUN.
