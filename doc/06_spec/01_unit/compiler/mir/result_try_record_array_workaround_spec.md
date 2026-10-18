# Typed Result record binding workaround

REQ-MIR-TRY-RECORD-ARRAY-WA-001. Manually documented executable SSpec;
docgen, parsed/MIR scenarios, native execution and required core/MCP checks
are UNRUN. This package does not include or qualify the compiler root fix.

1. Parse a real imported provider and a consumer homonym, state ProviderBundle
   on the Result Ok binding, retain ordinary for-in, and assert one producer
   call plus array length/get and Result discriminant/payload operations.
2. Parse the same-module producer returning the imported ProviderBundle;
   require the same real operations and one produce_local invocation.
3. Parse an annotated record with integer rows; require the specific non-array
   diagnostic and no array-get operation. An annotation must not admit a scalar.

Native counterpart: `test/fixtures/compiler/result_try_record_array/typed.spl`
and its checked-in sibling `provider.spl`. It asserts imported success37,
local success41, exact imported/local Err messages, exit0, empty stderr and
stdout `RESULT_TRY_RECORD_ARRAY_PASS cases=4` plus LF. Its only semantic
source differences from the separately retained root-fix native fixture are
two explicit ProviderBundle bindings. No unannotated acceptance test is added
to this release package without the compiler repair.

The production workaround states NativeGroupResultV1 and
NativeGroupWarmRouteV1 on the original grouped-parent Result bindings.
Question-mark propagation, ordinary loops, process/result/dependency validation
and persistence remain unchanged. A current admitted producer can eventually
qualify this source workaround; only a producer containing the separate
71b46ad repair can qualify removal of those annotations. No build or runtime
execution is authorized by this document.
