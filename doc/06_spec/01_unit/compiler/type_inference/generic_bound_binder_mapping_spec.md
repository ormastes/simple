# Generic bounds retain the declared binder position

Authored companion to `test/01_unit/compiler/type_inference/generic_bound_binder_mapping_spec.spl`.
Requirement REQ-GENERIC-BOUND-BINDER-MAPPING. All eleven scenarios and docgen UNRUN;
this manual is authored source documentation, not generated execution evidence.

## Setup and operation

Parse two real trait declarations and a three-binder function. Require the
expected lowered declarations and type-parameter count. Attach a bare named
trait bound to U, or two bounds to V, using those declarations' actual IDs.
Collect the metadata through HmInferContext and register a real ImplBlock for
i64 through the existing TraitSolver API. Missing fixtures fail explicitly.

| Scenario | Required result |
|---|---|
| Invalid second argument | `<i64,bool,i64>` produces a Bool obligation with U's actual symbol and fails the actual solver |
| Valid second argument | `<bool,i64,bool>` produces an i64 obligation and succeeds with no HM errors |
| Sparse third binder | Two bounds on V both use the third argument, preserve distinct trait records/order and solve |
| Missing metadata | Registered bounds without declaration context, or legacy helper without order, produce precise HM diagnostics and no obligation |
| Incomplete vector | A short type-argument list is diagnosed before an obligation is created |
| Module collision | A second owner is refused and the first context's binder metadata remains intact |
| Wrong trait kind | A real symbol row changed to Struct cannot become a trait obligation |
| Foreign parameter owner | A parameter row explicitly marked as another owner is diagnosed |
| Recollection | Removing the bound and recollecting the same owner removes stale obligations metadata |
| Parameterized trait payload | A nonempty Named trait argument list is diagnosed before any argument-erasing solver call |
| Constructor and position controls | Both constructors initialize nil authority; absent/duplicate binder positions are diagnosed |

Metadata checks assert the HM error list, not merely an empty solver queue.
The helper APIs queue obligations; callers must consider those HM errors before
using solver success as admission. Tests use real solver results for the valid
and invalid type cases, including actual pending cause symbols and source spans.

## Remaining acceptance

No compiler, runtime or native execution was performed. These API tests do not
prove inline source-bound parsing or active driver integration. The current
infer_module path does not collect/solve these obligations, and Var-only call
generation lacks complete inferred/default/NamedVar/method owner transport.
The companion bug report lists the exact follow-up owner work. Full bound
admission and the original G2/G3/G7 scope remain open.
