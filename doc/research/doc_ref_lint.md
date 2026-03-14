# Research: Doc Reference & SDoctest Lint

**Feature:** `doc_ref_lint`
**Related:** [requirement](../requirement/doc_ref_lint.md)

---

## Codebase Findings

### Lint Pass Pattern
- All lint passes in `src/compiler/35.semantics/lint/`
- Pattern: Warning struct + `check_*` entry point + helper functions
- Use arena-based core AST (`compiler.core.ast`, `compiler.core.ast_expr`)
- Reference implementation: `stub_impl.spl` (430 lines, closest pattern)

### Doc Comment Storage
- AST: `has_doc_comment: bool` + `doc_comment: text` on every declaration
- HIR: `doc_comment: text` on HirFunction, HirClass, HirStruct, HirEnum
- Frontend: `doc_gen.spl` extracts `"""..."""` blocks
- Doc comments are plain text — no structured markup parsed yet

### Existing Infrastructure to Reuse
- `body_references_any_param()` in `stub_impl.spl` — adapt for PDOC003 body usage check
- `body_has_pass_marker()` in `stub_impl.spl` — reuse for exempting pass_todo fns
- `__init__.spl` already exports `public_doc.*` — file just needs to exist

### Core AST Access
- `decl_tag[idx]` → declaration type (DECL_FN, DECL_CLASS, DECL_STRUCT, etc.)
- `decl_name[idx]` → name
- `decl_doc_comment[idx]` → doc comment text (need to verify field name)
- `decl_body_stmts[idx]` → function body statements
- `decl_visibility[idx]` → public/private (need to verify)

### sdoctest Detection
- Look for `sdoctest:` marker in doc comment text
- Already tracked by doc-coverage tool via grep

### No Existing Reference Syntax
- No `@see`, `@link`, `@ref` in any doc comment currently
- Clean slate for introducing new markers
