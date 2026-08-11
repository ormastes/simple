# compile_c_entry flat-AST bridge lowers EVERY binary op to Add and EVERY unary to Neg

- **ID:** compile_c_entry_flat_ast_all_binaries_lower_to_add_2026-08-11
- **Status:** OPEN
- **Severity:** HIGH (silent miscompile — wrong answers, no diagnostic)
- **Found:** 2026-08-11, while root-causing the SimpleOS WM rung-(d) text-render blocker
- **Lane:** `src/app/cli/compile_c_entry.spl` (C-entry / flat-AST bridge). **NOT** the
  `--entry-closure` freestanding lane, and not the default `run`/`test` pipeline.

## Defect

`src/compiler/70.backend/backend/compile_c_entry.spl:109-117`, in `convert_flat_expr`:

```
    elif tag == EXPR_BINARY:
        val left = convert_flat_expr(expr_left[idx])
        val right = convert_flat_expr(expr_right[idx])
        # Binary op stored as token kind in i_val; default to Add for now
        Expr(kind: ExprKind.Binary(BinOp.Add, left, right), span: span)
    elif tag == EXPR_UNARY:
        val operand = convert_flat_expr(expr_left[idx])
        Expr(kind: ExprKind.Unary(UnaryOp.Neg, operand), span: span)
```

The operator is discarded. `expr_i_val[idx]` — which the comment itself says holds the
token kind, and which the function already reads for other tags — is never consulted.
Consequences on this lane:

| source | actually compiled as |
|--------|----------------------|
| `a and b` | `a + b` |
| `a or b` | `a + b` |
| `a != b` | `a + b` |
| `a == b` | `a + b` |
| `a - b`, `a * b`, `a / b`, `a % b`, shifts, comparisons | `a + b` |
| `not x` | `-x` |
| `-x` | `-x` (only correct case) |

Only `+` and unary `-` survive. Everything else is a silent wrong answer: no parse
error, no type error, no warning. A predicate compiled through this path returns an
arithmetic sum, which is then truthy for almost every input.

## Root cause

This is the **same defect class as #148**, which was fixed in the *other* flat-AST
converter but never propagated here. The correct decoders already exist and are
already used:

- `src/compiler/.../_FlatAstBridge/convert_nodes.spl:519-541` — `op_kind_to_binop`
  and `op_kind_to_unaryop`.

`compile_c_entry.spl` was simply not updated when #148 landed. The `# ... default to
Add for now` comment is the original author self-documenting the placeholder; it was
never revisited.

## Fix

Replace the two hardcoded constructions with the decoded operator, reusing the
existing helpers rather than writing a third copy:

```
    elif tag == EXPR_BINARY:
        val left = convert_flat_expr(expr_left[idx])
        val right = convert_flat_expr(expr_right[idx])
        Expr(kind: ExprKind.Binary(op_kind_to_binop(expr_i_val[idx]), left, right), span: span)
    elif tag == EXPR_UNARY:
        val operand = convert_flat_expr(expr_left[idx])
        Expr(kind: ExprKind.Unary(op_kind_to_unaryop(expr_i_val[idx]), operand), span: span)
```

Both helpers must be reachable from `70.backend` — if they are not exported, lift them
to a shared module rather than duplicating the mapping (a third copy is how this
defect survived the #148 fix in the first place).

## Verification bar

A regression test must **discriminate the operator**, not merely execute the path. A
test whose only assertion is on `a + b` passes vacuously against this bug. Assert at
minimum: `2 - 1 == 1` (not 3), `1 != 1` is false (not 2), `not true` is false, and one
comparison in a branch condition. Sabotage the decoder and confirm the test goes RED.

## Discovery note

Found by a source audit of boolean-operator lowering while investigating the
freestanding entry-closure mixed `and`/`or` miscompile (the WM `text-font-batch` skip).
The two are **distinct defects on distinct lanes** and must not be conflated:

- This record: operator discarded at the flat-AST → `Expr` bridge, C-entry lane.
- The WM blocker: `and`/`or` LHS is fed to `terminate_if` without the 0/1
  normalization the RHS receives (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:2126-2183`),
  so a tagged/boxed bool LHS tests non-zero for both `true` and `false` — the
  "left operand is dropped" signature worked around at 5+ `src/lib` call sites.

Filed separately because this lane's defect is not reached by the WM gate and would
otherwise have survived only in a session transcript.
