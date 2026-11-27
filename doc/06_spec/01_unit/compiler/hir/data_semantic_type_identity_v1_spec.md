# Exact schema type binding through semantic owners

Source: `test/01_unit/compiler/hir/data_semantic_type_identity_v1_spec.spl`.
Status: authored manual; actual parser/nominal owner dependency integration,
admitted execution, docgen and maintenance verification pending.

| Scenario | Expected observation |
|---|---|
| Forward aliases | A real parsed forward alias and its direct nested target have equal descriptors before bodies are lowered. |
| SPL and SDN | A parsed generic class field and an independently parsed SDN expression use one prepared binding context and compare equal. A nested unsigned argument differs. |
| Semantic alias owner | Registered generic template defaults/substitution follow the existing owner; excessive arguments produce an error. |
| Nominal owner default | Parsed Box with omitted default and explicit i64 compare equal after the shared owner repair; excessive arguments fail. |
| Parsed generic aliases | The actual bridge retains its type parameters; default and explicit nested alias targets equal their direct types. |
| Alias errors | Cycles and unknown names produce no identity. |
| Nominal stability | RegionId and ObjId remain distinct; changing numeric symbol allocation while retaining declaration identity preserves the key. |
| Imported renames | Provider declaration, direct import alias and re-export alias compare equal through real retained module surfaces. |
| Provider homonyms | Equal leaf names from different modules remain different. |
| Alias collision | Importing Actual as Alias does not select an unrelated provider declaration named Alias. |
| Strict policy | Preparation reads parsed strict policy itself; reusing the context for a legacy module resets it. |
| Qualifiers | Ref/Ptr mutability and Isolated/Unique/Shared/Weak remain distinct, including nested qualifier position. |
| Function effects | Declared effects and Throws payload matter; effect order does not change the canonical key. |
| Unresolved metadata | Inference/error/parameter/projection and ownerless nominal metadata fail closed. |
| Type text | Checked parsing rejects malformed syntax, extra declarations, empty and NUL input. |
| Projection budgets | Wide HIR fails before collecting children; aggregate nodes are bounded across sibling subtrees. |
| Implicit erasure | Real parsed Q, nested Q, container/nominal arguments, tuple/function children and bare Dict lower without diagnostics but cannot enter concrete schema admission. |
| Written Any | Ordinary unsafe written-Any permission cannot admit Any or nested Any to this concrete schema slice. |
| Alias erasure/defaults | Parsed erased alias targets/defaults fail; an explicit concrete generic argument succeeds. |
| Declared Q control | A real nominal Q and nested aliases using it bind successfully. |
| Semantic policy traversal | Every projected child shape, including function Throws, rejects Any only in concrete mode; transport still represents it and concrete function controls preserve the exact descriptor. |

These are expected assertions, not executed results. No successful runtime,
full-W1 admission or compiler qualification follows from this manual alone.
