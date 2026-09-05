# Removal record: AST-based type-inference cluster in `30.types/type_system/`

Date: 2026-08-01
Decision: **DELETE**
Base commit (verified identical to WC before edit): `f3aa4091fecfaaacbc1ef31bfd98fc96bf9a2d88`

## What was removed

Source (3,107 LOC, `src/compiler/30.types/type_system/`):

| File | LOC |
|---|---|
| `expr_infer.spl` | 545 |
| `expr_infer_ops.spl` | 255 |
| `expr_infer_calls.spl` | 306 |
| `bidirectional.spl` | 530 |
| `module_check.spl` | 611 |
| `stmt_check.spl` | 17 (re-export shim) |
| `type_utils.spl` | 17 |
| `_StmtCheck/bindings_check.spl` | 623 |
| `_StmtCheck/verification_check.spl` | 203 |

Edited, not deleted:

- `checker.spl` — dropped the 4 cluster imports, the 5 "Integrated Type
  Inference" methods (`check_module`, `infer_expr_with_context`,
  `infer_expr_simple`, `check_stmt_integrated`, `check_block_integrated`) and
  `create_engine`. `enum TypeError` (the file's only external consumer),
  `TraitImplRegistry`, `MixinInfo` and the self-contained parts of
  `class TypeChecker` are kept. A scope warning was added to the file header.
- `__init__.spl` — dropped the re-export block naming the deleted modules.

Tests (orphaned fake-passes whose subject no longer exists) removed from both
`test/01_unit/compiler/type_inference/` and `test/unit/compiler/type_inference/`
(spec + `.spipe_matchers_*` variant + result dir):
`bidirectional_spec.spl`, `expr_inference_spec.spl`, `module_check_spec.spl`,
`stmt_check_spec.spl`. Each had its entire body commented out and a single
`it "skipped"` asserting `pending_reason.len() > 0` — a permanent green that
implied coverage of code that could not run.

## To recover any of this

    git show f3aa4091:src/compiler/30.types/type_system/expr_infer.spl

…and likewise for the other paths above.

## Why DELETE

The "keep it, it encodes design intent" argument is void here because the intent
already exists as a *live* implementation. The driver's real type-check path is
`HmInferContext` (`src/compiler/30.types/type_infer/`, HIR-based), wired on
2026-07-05 by `0cc41c9914b` and called from `run_typecheck_warn_pass()` in
`src/compiler/80.driver/driver_hir_pipeline_passes.spl:68` under
`SIMPLE_TYPECHECK_WARN=1`. The deleted cluster was a parallel *AST-based* engine
that lost that contest and was never connected: a pickaxe over the whole history
for `type_system.expr_infer` and `type_system.bidirectional` outside the cluster
directory returns **zero commits** — it was never wired, so there is no
disconnection event to weigh and no regression to restore. It also could not
have worked: `infer_expr`/`check_expr` match the **struct** `Expr`
(`10.frontend/parser_types_expr.spl:204`) against `ExprKind`
(`:210`) variant names, so every arm was dead, ~26 called helpers have zero
`fn <name>` definitions repo-wide, and silent `case _:` fallbacks
(`bidirectional.spl:287`, `module_check.spl:560`) swallowed the rest. Keeping
3,107 LOC of live-looking, never-executed inference code violates the repo's
"never keep unused code" rule and is precisely the hazard that already misled
five-plus bug docs into citing dead files as evidence.

## Entry-point verification method (reproducible)

Anchor on **import lines**, never the bare module name — matching `check_expr` or
`synthesize_expr` as bare identifiers hits unrelated files that happen to define
those generic names, which is how a dead module got reported as wired.

    /usr/bin/grep -rn --include=*.spl -E '^[[:space:]]*(use|import|from)[^\n]*type_system' src/ test/ \
      | /usr/bin/grep -v '^src/compiler/30.types/type_system/'

Before removal this returned exactly 5 lines, none reaching the cluster:

- `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:31` → `effect_pass.{run_effect_pass}`
- `src/compiler/90.tools/query_helpers.spl:8` → `checker.{TypeError}` (a type only)
- 3 spec files → `effect_pass.{run_effect_pass}`

(The earlier audit reported 2; it missed the 3 `effect_pass` specs. They do not
change the conclusion — `effect_pass.spl` imports nothing from the cluster.)

A second pass anchored on the module **basenames** on import lines
(`bidirectional|expr_infer|expr_infer_ops|expr_infer_calls|module_check|stmt_check|type_utils|builtin_registry`)
returned 36 lines, **all 36 inside the cluster directory itself** — a closed
island. Non-`.spl` references were also swept: the only hits were a synthetic
temp-dir path inside a Rust `module_resolver` unit test
(`src/compiler_rust/compiler/src/module_resolver/mod.rs:313`) and a
`parse_debug.rs` fixture naming `effects.spl` — neither is a build dependency.

Post-removal, the dangling-reference grep for the deleted module paths and
`_StmtCheck` returns **0** across `src/` and `test/`.

## Not verified by compilation

`bin/simple` SIGILLs on every compile at HEAD (fix in source, deploy pending),
and `simple test` silently delegates to the Rust seed child, so no build or test
run backs this change. The evidence is static: zero importers before the change,
zero dangling references after. The next successful bootstrap is the real gate.
