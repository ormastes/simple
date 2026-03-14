# Design: Doc Reference & SDoctest Lint

**Feature:** `doc_ref_lint`
**Related:** [requirement](../requirement/doc_ref_lint.md) | [plan](../plan/doc_ref_lint.md) | [research](../research/doc_ref_lint.md) | [test](../../test/unit/compiler/lint/public_doc_spec.spl)

---

## Architecture

### Integration Points

```
Source text (.spl)
  ├─→ 35.semantics/lint/public_doc.spl     → [PublicDocWarning]  (lint pass)
  └─→ 90.tools/fix/rules/impl/lint_public_doc.spl → [EasyFix]   (fix tool)
                                 ↓
              90.tools/fix/rules/registry.spl       (rule dispatch)
```

### Why Text-Based

Doc comments (`"""..."""`) are NOT stored in the arena-based core AST (`compiler.core.ast`). The arena tracks `decl_is_pub`, `decl_name`, `decl_body_stmts` etc. but has no `decl_doc_comment` field. Therefore this lint operates on source text directly, consistent with `doc_coverage_dynamic.spl` and other text-scanning fix rules.

### Module Layout

| File | Exports | Role |
|------|---------|------|
| `35.semantics/lint/public_doc.spl` | `PublicDocWarning`, `check_public_doc` | Core lint logic |
| `90.tools/fix/rules/impl/lint_public_doc.spl` | `check_public_doc_text` | EasyFix wrapper |
| `35.semantics/lint/__init__.spl` | re-exports `PublicDocWarning`, `check_public_doc` | Lint module API |
| `90.tools/fix/rules/impl/__init__.spl` | re-exports `check_public_doc_text` | Fix tool API |
| `90.tools/fix/rules/registry.spl` | calls `check_public_doc_text` | Rule dispatch |

## Data Flow

1. Source text split into lines
2. **Pass 1**: Scan for `"""` blocks and declarations at indent 0, building parallel arrays:
   - `decl_names`, `decl_kinds`, `decl_docs`, `decl_line_nums`
3. **Pass 2**: Compute body end lines (next declaration or EOF)
4. **Pass 3**: For each declaration, extract `@see(X)` / `@sdoctest(X)` refs, check PDOC001-005

## Reference Syntax

Inside `"""..."""` doc comments:

```
@see(name)        — cross-reference to another fn/class/struct in same module
@sdoctest(name)   — delegate sdoctest examples to name's docstring
```

Parsed by scanning each doc line for the marker, extracting the name between `(` and `)`.

## Lint Rules Summary

| Code | Applies To | Condition |
|------|-----------|-----------|
| PDOC001 | public `fn`, `class` | No `sdoctest:` block AND no `@sdoctest(X)` |
| PDOC002 | any decl with refs | `@see(X)` or `@sdoctest(X)` where X not in module |
| PDOC003 | `fn` with `@see` | X exists but not referenced in function body |
| PDOC004 | `fn`/`class` with `@sdoctest` | X's kind doesn't match declaration's kind |
| PDOC005 | any decl with `@sdoctest` | X itself has no sdoctest block |

## Exemptions

- `extern fn` — no body, no sdoctest possible
- Functions starting with `_` — private by convention
- Functions containing `pass_todo`, `pass_do_nothing`, `pass_dn` — explicitly marked as unfinished
