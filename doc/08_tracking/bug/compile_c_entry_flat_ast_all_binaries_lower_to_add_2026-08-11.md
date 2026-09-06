# compile_c_entry flat-AST bridge lowers EVERY binary op to Add and EVERY unary to Neg

- **ID:** compile_c_entry_flat_ast_all_binaries_lower_to_add_2026-08-11
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
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

## Verification status (2026-08-11)

The source fix is applied exactly as prescribed above: `compile_c_entry.spl` now
imports `op_kind_to_binop` / `op_kind_to_unaryop` from
`compiler.frontend.flat_ast_bridge` (they are already re-exported there via
`export use compiler.frontend._FlatAstBridge.convert_nodes.*`) — no third copy of the
mapping was written. The module loads clean under `bin/simple run` with no
`[use-warning]` for either symbol, so both names resolve.

**The mandated discriminating regression test could not be made to run.** Two
independent blockers, both pre-existing and both measured, not assumed:

1. **Name collision defeats an out-of-module unit probe.** There are two functions
   named `convert_flat_expr` (`compile_c_entry.spl:79` and
   `_FlatAstBridge/convert_nodes.spl:729`). The tree-walk interpreter resolves the
   import by NAME and binds the *frontend* copy. Proven by sabotage: setting
   `BinOp.Add` -> `BinOp.Sub` at `compile_c_entry.spl:114` left a probe importing
   `convert_flat_expr` fully GREEN — i.e. a probe written that way is a **false
   green** against this exact bug. Temporarily renaming the local function made the
   sabotage visible, which confirms the collision.
2. **Backend module's flat-AST globals are a separate, empty instance.** With the
   rename in place the probe reaches the right function and immediately dies with
   `array index out of bounds: index is 2 but length is 0` on `expr_tag[idx]` —
   `compile_c_entry` reads the raw `expr_tag` / `expr_left` globals, and driving
   `parser_init` + `parse_module_body` from another module does not populate the
   view that module sees. (The frontend copy avoids this by using the
   `expr_get_tag` accessors.) The converter is therefore only exercisable when
   `compile_c_entry.spl` is itself the entry module.
3. **That entry lane is independently RED.** `bin/simple run
   src/compiler/70.backend/backend/compile_c_entry.spl <probe.spl> <out.cpp>`
   (Cranelift JIT, which falls back to the interpreter here) reports
   `Step 2: Done (HIR functions: 0)`, `Step 3: Done (MIR functions: 0, types: 0)`
   and then fails with `error: semantic: class 'MirToC' has no field named
   'str_locals'`, emitting no `.cpp`. This failure predates and is independent of
   the operator fix.

No vacuous test was committed in place of the real one. Re-attempt the
discriminating test once the C-entry lane compiles a hello-world end to end; the
assertions to use are the ones in the "Verification bar" section above.

## Sweep

`/usr/bin/grep -rn --include=*.spl "ExprKind.Binary(BinOp.Add" src/` returns exactly
one hit — this file. The sibling `src/app/cli/compile_c_entry.spl` is a thin argv
wrapper around `aot_c_file` and contains no flat-AST conversion, so it does **not**
carry the defect. The family has one member.

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
