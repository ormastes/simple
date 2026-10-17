# Indirect call declared return owner

Executable specification: `test/01_unit/compiler/mir/indirect_call_return_owner_spec.spl`.

The specification invokes real MIR lowering and inspects diagnostics, retained
HIR ownership, result types and emitted indirect-call signatures.

| Scenario | Required evidence |
| --- | --- |
| Imported callback return with competing short name | Provider-qualified owner rebinds to consumer symbol 77. |
| Foreign ID without exact owner | Resolution fails instead of accepting the colliding symbol. |
| Record callback result | Declared owner, canonical layout and record MIR type survive emission. |
| Already projected callback | Shared argument lowering does not evaluate the invalid receiver again. |
| Unresolved declared return | Fatal diagnostic; no guessed record result. |
| Narrow callback parameter | Both closure and raw call arms retain I32 parameter and Bool result. |
| Callback arity mismatch | Fatal argument-count diagnostic before indirect emission. |
| Unresolved declared parameter | Fatal parameter-type diagnostic instead of word-ABI guessing. |

Status on 2026-10-16: updated specification; execution remains pending a usable
test runtime. Static review and native compiler build evidence are separate
from an executed specification result.
