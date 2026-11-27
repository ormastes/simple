# Complete semantic type identity transport

Source: `test/01_unit/compiler/data/data_semantic_type_identity_v1_spec.spl`.
Manual status: authored companion; admitted docgen/sspec-maintain and execution
are pending. No passing execution or coverage result is implied.

| Scenario | Operation and expected result |
|---|---|
| Nested qualifiers | Encode Box with mutable versus immutable reference argument. Identical full keys compare equal; the nested qualifier change compares unequal. |
| Nominal declarations | Change only module, terminal name, or declaration kind. Equal machine representation does not merge these types. |
| UTF-8 length | Round-trip non-ASCII module/name fields using byte framing. Reject an inconsistent explicit byte length. |
| Version/framing | Reject wrong version, trailing suffix, noncanonical counts, truncated field and empty input. |
| Constructor/arity | Reject inference/alias carriers, missing/extra children, effects in type positions, and oversized function counts before arithmetic. |
| Finite budgets | Reject a too-deep tree and an over-1024-node balanced tree whose byte size remains within the byte cap. |
| Digest collision | Keep two complete type descriptors in the same forced bucket; exact comparison finds only the matching descriptor. |

The descriptor is transport for a semantic owner. These scenarios do not claim
that arbitrary spelling has been resolved, an alias has been semantically
checked, a schema is admitted, or the full node-attribute feature is complete.
