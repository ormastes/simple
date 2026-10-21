# Enum semantic capture budget

Requirements: EE-01, EE-PV05. Status: authored; execution and documentation generation **UNRUN**.

The fixture parses `Budget` with source discriminants 7, 42 and 43, clones the actual source symbol environment, and calls `prepare_enum_semantic_declarations_v1`. It starts a fresh MIR function builder using the actual HIR function symbol, then invokes `enum_semantic_begin_v1`, `enum_semantic_select_owner_v1` and `enum_semantic_pattern_v1`. No alternate capture implementation supplies the result.

Setup pins the named source-owner mapping, function ownership, one initial capture debit, one match count and an empty pattern vector. Each scenario explicitly replaces the actual function's work counter and reads it back using dictionary lookup; dictionary cardinality is never an oracle.

| Scenario | Initial used / remaining | Required observation |
|---|---|---|
| Variant scan exhaustion | 65534 / 2 | Capturing nullary `First`, which already matches the first declaration, still exhausts the actual three-variant name scan. Result is -1, diagnostic is `EE-E-LIMIT: function capture budget`, used work is 65536, and no pattern node is published. Removing scan charges makes this case incorrectly succeed. |
| Exact sufficient control | 65528 / 8 | `Pair(_, _)` charges one root, three variant comparisons, two payload copies and two child nodes. It succeeds at work 65536 with root index 2, discriminant 43, children `[0, 1]`, exact source owner and ordered `I64`, `Bool` slots. Missing either scan or copy charges changes the observed counter. |
| Arity before copy | 65532 / 4 | `Pair(_, _, _)` exhausts available work on the root and variant scan, then returns the exact payload-arity diagnostic with no nodes. Any attempted copy debit would instead produce the limit diagnostic, so the result distinguishes the required ordering. |

These are source-authored actual-API boundary controls for revision 2. They establish no executed compiler, native, performance or proof acceptance.
