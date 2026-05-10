# Audit: Math Blocks (`m{}`, `loss{}`, `nograd{}`)

**Date:** 2026-04-04
**Feature:** Math block DSL syntax and editor integration

## Implemented Core

- **Lexer/Parser (Rust):** `src/compiler_rust/parser/src/lexer/identifiers.rs:354-463` -- `m{`, `loss{`, `nograd{` recognized as custom block payloads
- **Block Definitions (Simple):** `src/compiler/15.blocks/blocks/builtin_blocks_math.spl:145-329` -- `MathBlockDef`, `LossBlockDef`, `NogradBlockDef` implementing lexer, highlight, outline, parse_payload, skip_policy
- **Block Registry:** `src/compiler/15.blocks/blocks/registry.spl:54-56` -- all three registered
- **HIR Resolve:** `src/compiler/35.semantics/resolve.spl:514-518` -- `LossBlock`/`NogradBlock` resolved via `resolve_block()`
- **Safety Check:** `src/compiler/35.semantics/safety_checker.spl:200-203`
- **MIR Lowering:** `src/compiler/50.mir/mir_lowering_expr.spl:198-202`, `mir_lowering_ml.spl:48-94` -- dispatches to `lower_loss_block()` / `lower_nograd_block()`
- **Rendering Library:** `src/lib/common/math_repr.spl` -- full AST parser producing 5 output formats (text, debug, pretty, markdown, LaTeX)
- **VSCode Extension:** `src/app/vscode_extension/src/math/{mathDecorationProvider,mathConverter,mathHoverProvider,mathPreviewPanel}.ts` -- conceals delimiters, Unicode preview, hover, panel
- **Neovim Plugin:** `src/app/nvim_plugin/lua/simple/math.lua` -- block detection, extmark concealment, Unicode rendering, float-on-hover
- **Treesitter:** `src/compiler/10.frontend/parser/treesitter/queries/highlights.scm:531-533` -- `@embedded.math` highlighting

**Syntax features:** `^` power, `'` transpose, implicit multiplication (2x), broadcast operators (`.+`, `.-`, `.*`, `./`, `.^`), `@` matrix multiply, Greek letter auto-conversion, `frac()`, `sqrt()`, `sum()`, `int()`, `product()` binders.

## Known Limits

1. ~~**`loss{}` and `nograd{}` autograd semantics are stubs**~~ -- **RESOLVED**: `mir_lowering_ml.spl` now emits real `rt_torch_autograd_backward` (loss) and balanced `rt_torch_autograd_no_grad_begin/end` (nograd) with failure-safe block patching for early-exit paths
2. **Custom block codegen returns unit placeholder** -- `mir_lowering_ml.spl:39-42`: blocks return unit; actual evaluation happens via interpreter
3. **LaTeX rendering gaps** -- no AST nodes for derivatives (`diff(f,x)`), limits (`lim(f,x,0)`), or text annotations (per `doc/09_report/2026/02/math_rendering_limitations_2026-02-01.md`)
4. **Interpreter-mode test limitation** -- `it` block bodies do not execute; 28 passing math_blocks_spec tests confirm parse/load only

## Proof References

| Layer | Files |
|-------|-------|
| Rust lexer | `src/compiler_rust/parser/src/lexer/identifiers.rs:354-463` |
| Block defs | `src/compiler/15.blocks/blocks/builtin_blocks_math.spl` |
| Block registry | `src/compiler/15.blocks/blocks/registry.spl:54-56` |
| HIR resolve | `src/compiler/35.semantics/resolve.spl:514-518` |
| MIR lowering | `src/compiler/50.mir/mir_lowering_ml.spl:48-94` |
| Rendering | `src/lib/common/math_repr.spl` |
| Treesitter | `src/compiler/10.frontend/parser/treesitter/queries/highlights.scm:531-533` |
| VSCode | `src/app/vscode_extension/src/math/` (4 files) |
| Neovim | `src/app/nvim_plugin/lua/simple/math.lua` |
| Tests | `test/feature/usage/math_blocks_spec.spl` (28), `loss_nograd_blocks_spec.spl`, `math_render_spec.spl`, `math_dl_equations_spec.spl`, `math_language_spec.spl`, `implicit_mul_spec.spl` |
| Limitations | `doc/09_report/2026/02/math_rendering_limitations_2026-02-01.md` |

## Recommended README Wording

> **Math blocks** (`m{}`, `loss{}`, `nograd{}`) -- inline DSL with `^` power, `'` transpose, implicit multiplication, broadcast operators, and `@` matrix multiply; renders to LaTeX and Unicode in VSCode and Neovim editors via LSP hover and inline decoration; `loss{}` triggers auto-backward on the torch autograd backend; `nograd{}` provides failure-safe gradient suppression with RAII guard and MIR-level cleanup on all exit paths
