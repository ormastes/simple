# MCP MIR array return and field erasure

Status: OPEN. Candidate workaround is NOT runtime-qualified; do not claim the MCP build works.

Independent failure collection: p2-mcp-sosix-stdio/mir-failures.json has 14 unique MIR errors after HIR141 modules. Six foreach collection types are I64 on imported Option payload/array fields, one JSON nested loop is Tuple, and database parse reaches Infer from raw_cols.map(&:trim). Other method-resolution failures remain separate.

Exact focused reproduction imports real std.common.json.types.json_to_array and iterates its nullable result. Baseline native compilation exits1 in4.633s with the same Tuple foreach rejection. Source is a real Git-owned isolated checkout based on523ce4c9b47f81f1472f121bcac84a4238fb5c76.

Candidate strengthens json_to_array return from any? to [any]? and explicitly unwraps the nested array with typed `?? []`; flatten workaround tag mcp-mir-json-array-return-20261012. Return typing alone still rejects Tuple. Typed nullable unwrapping emits a16928-byte object in4.811s, link0, but actual runtime exits41 (expected two nested elements). The candidate is semantically unverified. Three distinct source fix/verification cycles cap reached; no broad compiler rebuild or unchanged repeat.

Evidence directories under /mnt/c/Temp: simple-mcp-mir-contract-baseline-20261012, simple-mcp-mir-contract-returntype-committed-20261012, simple-mcp-mir-contract-unwrapped-20261012. First dirty-source trial did not observe its source edit and is not a fix verification. JSON actual worker source snapshot signature was checked in the committed trial.

Separate committed minimal Option/class array field fixture covers imported Table?/Some(table).rows and list_tables()[].rows with expected sum19. Its qualification is tracked independently and cannot be inferred from JSON object generation.

Field qualification: baseline emitted two matching I64 foreach failures in5.544s. Explicit imported Table receiver, [Entry] array binding, and Entry element binding emitted4416-byte object in4.251s; manual link0, native execution0 verifies expected sum19. Workaround tag mcp-mir-array-field-erasure-20261012. This is a scoped workaround PASS, not a compiler logic repair or aggregate MCP PASS. Diagnostic source-only compiler trace was not observed, so there is no evidence the existing producer executed edited expr_dispatch source; the diagnostic instrumentation was removed.

Authorized isolated application candidates annotate six MCP array-field loops (assistant2, context1, logopt1, telemetry2) and database validation SdnRow receiver; every annotation carries the field-erasure workaround tag. Database parse map(&:trim) is separately expanded to typed text-array iteration under tag mcp-mir-database-map-infer-20261012 because actual MIR reports Infer at that expression. Database public API fixture checks trimmed header columns and key/value row method results. These production applications require their own compilation; the prior Table fixture PASS is not aggregate MCP or database PASS.

Database production candidate qualification: public API fixture cleared all51 HIR/MIR/native-cache modules with zero reported compiler errors. Native compilation progressed11/51 by46.295s, then the90s deadline returned124 without a final object. Thus original Infer/get errors were absent in this focused closure, but object/link/execution remain unverified. Partial native cache is preserved in the isolated checkout; no identical retry was made. Across this whole isolated diagnostic lane29 object-cache files (851072 bytes) exist, a mixed-lane cache inventory and not a count of completed database modules. No owned compiler worker remained after termination.
