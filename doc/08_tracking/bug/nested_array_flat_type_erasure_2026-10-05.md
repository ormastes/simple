# Nested array declarations erased before MIR projection

Status: source repair prepared; six new unit cases and the existing native array fixtures remain unverified with a rebuilt producer.

Producer c5a40876fdbd01cff8cae7e3105a0977af60458e9f346803576da456ba7ee05c, source3015a0836bfd9e2f32a2718334fad2423ccd77f5, passed actual Hello with Cranelift and LLVM. Both backend builds of the original20-check array fixture failed with three unresolved indexed sort/pop/clear calls. Both builds of the six-check projected fixture failed with seven unresolved indexed mutation calls. No array assertions executed. The field text pop that previously failed now reaches the typed array path.

One failed-only Cranelift trace is preserved at runtime/windows-restart-20261004/array-index-provenance-3015-trace1, collector complete/raw1. Its full native worker stderr identifies writeback kind1 for all seven failures, while field pop uses kind2 and enters array dispatch. No debugger or process dump was used.

The associated complete HIR cache is 2f95055a041a1914375df9affeba257aa3ec9a08d0166f4edad37f1738f5766b.hir, SHA2563693a204a228ae05c9a5f2c84eef3c97eaa078412565fb16375a6711d7aa4e94. Its symbol table encodes `nested`, `deep`, and `WordBox.rows` as Array(Any), using the generated codec's Array tag7 and Any tag24. The source declares `[[text]]`, `[[[i64]]]`, and `[[i64]]` respectively. Thus MIR's refusal to classify Any as an array is correct; the prior projection helper could not recover a declaration already erased upstream.

The flat parser explicitly routed any dedicated array element tag to TYPE_ARRAY_ANY. Remove that obsolete branch. Nested element tags now use the existing array specialization registry, which is recursively decoded by convert_flat_type and already serialized/restored by flat_type_pools_dump/restore. No cache format, runtime representation, array ABI, unknown-type guard, mutation method dispatch or single-evaluation/writeback behavior changes.

Regression coverage includes two/three nesting levels, text/bool/fixed-width leaves, unchanged dedicated scalar-array tags, a real flat-pool reset/restore, and HIR encode/decode of nested parameter declarations. Specs use global flat pools and require an isolated test process. The existing native_array_projected_mutations.spl (six checks) and native_array_mutation_methods.spl (20 checks) remain the runtime oracle on both backends after producer refresh. No passing native result or performance improvement is claimed.
