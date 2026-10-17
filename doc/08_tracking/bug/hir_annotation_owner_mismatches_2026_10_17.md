# Incorrect owner annotations in AST and HIR extractions

Date: 2026-10-17
Bug: BUG-HIR-ANNOTATION-OWNER-MISMATCHES-20261017
Database registration: pending; no admitted database tool available.
Status: source-confirmed; native regression and broad compiler gates UNRUN.
Affected source: 6a3a83bc0674596f29dfa8cd2445b8d965e51566.

The recent explicit extraction annotations selected incompatible record or container owners at nine sites, plus one missing selected import. These are concrete source errors; this report does not claim an executed reproduction.

Four parser argument extractions in module_callable_types (656,953,963) and expression_support (319) used HirCallArg. Frontend ExprKind.Call and MethodCall carry [CallArg] (parser_types_expr:484-485), whose value is Expr. HirCallArg instead carries HirExpr. Restore the frontend CallArg owner already available through the existing frontend import.

Three Range bound rebinds in match_desugaring (286,288,297) used parser Expr?. Their input is HirPatternKind.Range, whose bounds are HirExpr (hir_definitions:766). Use HirExpr? to preserve the existing nullable-bound handling and HIR expression owner.

statements:161 indexed struct_field_order_by_name but annotated its value with the entire HirFieldOrderByName dictionary alias. types:68 defines {text:[text]}; the selected value is [text]. Preserve the existing positional-field loop.

const_eval:491 annotated args[arg_idx] as HirExpr, although eval_const_fn_call:462 declares args:[HirCallArg] and then evaluates arg.value. Use the already explicitly imported HirCallArg. value_struct_layout:53 correctly extracts HirField from HirStruct.fields but lacked its selected declaration import; add HirField beside HirStruct.

The correction changes only these nine annotations and one import. Algorithms, indentation, diagnostics, receiver evaluation, ABI/schema checks and control flow are unchanged; exact inverse source proof is retained externally. No runtime workaround, permissive type-check fallback, enum payload ABI change, nil-span repair or dictionary iteration rewrite is included.

Validation: exact base/declaration witnesses and whole-file inverse checks cover all six production files; source guards and diff checks are recorded separately. No native/compiler/stdlib/MCP/LSP qualification is claimed. Bootstrap attempts remain exhausted3/3; this source correction authorizes no new build. Required future checks must exercise real parser calls, HIR ranges, struct positional field resolution and constant function arguments using an admitted compiler; generated annotation symmetry alone is not runtime evidence.
