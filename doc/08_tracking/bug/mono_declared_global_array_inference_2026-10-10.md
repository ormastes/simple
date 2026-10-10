# Generic array argument loses declared global pool type

Actual latest a0/aa404 object_record: all51 HIR modules pass, then nine E-MONO-032 at core/types.spl1523–1531, zero specializations, E-MONO-033, no MIR/object. PR2829 replaced erased promotion roots with _type_pool_promote_root<T>(root:[T]) applied to singleton arrays of explicit module-global [text]/[i64]/[[i64]] pools.

First source loss: HIR Ident produces untyped NamedVar; attached-type-only ArrayLit consensus cannot recover global type. Mono rewrite keeps metadata but infer_expr_type Var/NamedVar checks only function env then function signature. rewrite_function resets env and seeds params/lets; collect_generics omitted declared globals. Thus known declaration type never reaches argument inference. No explicit type-argument workaround or name-only guess is introduced.

Repair records concrete HirConst declaration types (including mutable pools), keyed by module identity and actual declaration.symbol.id, not constants dictionary key (bootstrap keys can be declaration indices). Lexical env retains precedence; fallback uses current_module and exact SymbolId; unknown/unregistered/nonconcrete remains uninferable. Four real source-lowering regression scenarios cover nested global array specialization, same numeric ID in distinct modules, lexical precedence and unknown empty generic fail-closed. All UNEXECUTED. Fresh producer/object gate required; no runtime/SPipe PASS claimed.

Follow-up source review found the imported-global variant was not covered by
those provider-local cases. HIR import registration creates an exact consumer
`SymbolKind.Const` alias with the projected type and `defining_module`, but
does not add a consumer `HirConst`. The pass now records concrete imported
Const aliases by the consumer module and alias SymbolId; it does not guess from
the leaf name. The added same-leaf two-provider fixture is authored and
UNEXECUTED, so this bridge has source evidence but no native result yet.
