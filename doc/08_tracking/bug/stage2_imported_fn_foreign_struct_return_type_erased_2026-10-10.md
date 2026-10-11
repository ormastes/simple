# stage2: unannotated local bound to an imported fn loses its struct type when the struct lives in a third module

Date: 2026-10-10. Lane: phase-2 subsystem test binaries (`test_interp`), stage2 `native-build --backend=llvm`.

## Symptom

`MIR lowering error: for-in over non-array iterables is not supported by native codegen yet (#143) ... (collection mir type: I64 ...)`

58 sites in the `test_interp` closure after its HIR errors were fixed:
`10.frontend/core/ast_clone.spl` (12), `type_subst.spl` (9),
`interpreter/_EvalOps/call_method_eval.spl` (9), `eval_stmts.spl` (7),
`_EvalOps/access_literal_assign_eval.spl` (7), `eval_decls.spl` (4), `eval.spl` (4),
`eval_calls.spl` (3), `eval_access.spl` (3). Every one is `for x in node.<array field>`
where `node` is an unannotated `val` bound to `expr_get`/`stmt_get`/`decl_get`.

## Minimal repro (three modules)

```
# nodes.spl
struct Node:
    names: [text]
fn make_node() -> Node: Node(names: ["a", "b"])

# state.spl
use nodes.{Node, make_node}
var node_pool: [Node] = []
fn node_get(idx: i64) -> Node:
    if node_pool.len() == 0: node_pool = node_pool.push(make_node())
    node_pool[idx]

# main.spl
use state.{node_get}
use nodes.{Node}
fn main():
    val src = node_get(0)          # FAILS: src.names is typed I64
    for name in src.names: ...
```

Measured with the stage2 binary of the 2026-10-10 full bootstrap:

| shape | result |
|---|---|
| `val src = node_get(0)` (fn in `state`, struct in `nodes`) | FAIL (#143, I64) |
| `val src: Node = node_get(0)` | lowers |
| `val src = make_node()` (fn and struct in the same imported module) | lowers |
| same, single file | lowers |
| `fn count(src: Node)` parameter | lowers |

So the declared return type of an imported function is dropped only when its
`Named` struct is owned by a module other than the function's own. The reader is
`resolved_call_hir_return_type` (`50.mir/_MirLoweringExpr/expr_dispatch.spl`); its
primary source `fn_return_types` has no writer anywhere in the tree, and the
name-keyed fallback is documented as carrying symbol-free shapes only.

## Not caused by

The `__init__.spl`-before-`mod.spl` resolver change: the repro has no package
directory at all.

## Also open in the same closure

5x `unsupported range index a[start..end]`, `unresolved method call: last_index_of`
(`eval_decls.spl`), `unresolved method call: repeat`.
