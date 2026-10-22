# MIR rejects supported brace struct literals

Status: OPEN. General compiler repair remains unimplemented.

Qualified new Phase2 producer1a9279 encountered McpStaticTool brace literal at src/app/mcp/main_static_tools.spl228. Current MIR expr_dispatch has an unconditional StructLit unsupported diagnostic E-MIR-EXPR-StructLit. The descriptor has three text fields name/desc/req, supplied as pure local reads in that identical order.

A tagged application workaround uses the already supported named constructor only at this verified site. It preserves values/order and does not forward arbitrary struct literals into lower_struct_construct: that helper evaluates declaration order, which can reorder side effects in a general literal. A real general fix must preserve source evaluation order, once-only effects, reordered named fields, and field types without application-specific compiler cases.

Reproducer: retain the original brace literal and actual failing MCP MIR receipt. Prevention must lower/execute reordered fields with effectful RHS in source order, compare field values, and reject unknown/duplicate fields. A sourcegrep test requiring the unsupported diagnostic is a fail-closed guard, not a feature qualification.

The isolated descriptor fixture copies the actual affected declaration/helper; nine native field assertions cover canonical descriptor strings, empties and Unicode/quoted required JSON. Actual native compile0/object7536B, strict paired C-provider link0/ELF2206408B, run0 with all9field assertions. Actual emitted failure branches resolve to rt_panic→spl_panic→exit; assertion sink is not a stub. This qualifies only the three-field pure-local descriptor helper under producer1a9279, not full MCP or the general compiler feature. Full core/check/MCP gates remain incomplete. No fourth whole MCP build.
