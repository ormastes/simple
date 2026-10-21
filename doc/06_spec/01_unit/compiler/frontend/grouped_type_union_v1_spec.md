# Parenthesized type grouping for the selected union source stage

Requirement: REQ-C2-UNION-TRANSPORT-001. Six actual parser/HIR scenarios are authored and **UNRUN**.

The flat parser previously discarded the only element of `(T)` and returned `TYPE_ANY`. It also parsed parenthesized elements without the existing union parser. The repair retains the one unseparated element, consumes existing union syntax within parentheses, and applies the existing Optional suffix operation afterward. It adds no raw union tag or new type grammar.

1. A nested `(bool | i64) | bool` retains both AST and HIR Union levels before semantic normalization.
2. `(i64)` is the actual primitive and `(i64)?` keeps the existing Option AST / Optional HIR boundary.
3. Labeled two-element tuples with trailing commas and the empty tuple retain exact arity/member order.
4. The separate existing `(i64,)` compatibility path remains the bridge's `__any` placeholder. This unresolved singleton-tuple behavior is not repaired or qualified here.
5. A function type retains both parameter types and its grouped union return; the arrow production remains prior to ordinary grouping.
6. `(i64 | bool)?` remains an outer Option/Optional containing a Union, without flattening its carrier. The selected union normalization stage still precisely refuses this unsupported outer carrier.

The public source-model union spec independently requires nested union introduction/elimination/export to succeed and inspects actual captured canonical declarations. Alias RHS parsing is unchanged. No compiler execution, parser test execution, native/Lean acceptance or memory/performance measurement is claimed.
