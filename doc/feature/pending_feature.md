# Pending Features

**Generated:** 2026-02-01
**Total Pending:** 4 features

## Summary

| Status | Count | Priority |
|--------|-------|---------|
| Failed | 0 | 🔴 Critical |
| In Progress | 0 | 🟡 High |
| Planned | 4 | 🟢 Medium |
| Ignored | 0 | ⚪ Low |

**Completion:** 0.0% (0 complete / 4 total)

---

## Progress by Category

| Category | Total | Complete | Pending | % Complete |
|----------|-------|----------|---------|------------|
| Syntax | 1 | 0 | 1 | 0% |
| Module System | 1 | 0 | 1 | 0% |
| Shell/DSL | 1 | 0 | 1 | 0% |
| Infrastructure | 1 | 0 | 1 | 0% |

---

## Implementation Priority

### Critical (Do First)

### High (Next Sprint)
3. Planned features with dependencies

### Medium (Backlog)

1. **Comma Decorator (Labeled Arguments)** — Syntax
   - Postfix label keywords (`to`, `from`) on function call arguments
   - Declaration: `fn copy_from(from: text to, to: text)`
   - Call site: `copy_from(src to, dst)` (comma-required)
   - **Decision:** Comma-optional (`copy_from(a to b)`) is rejected — ambiguous with keywords-as-identifiers, breaks LL(1), O(n^2) worst case
   - Design: `doc/design/comma_decorator_design.md`

2. **Structured Export** — Module System
   - Indented tree syntax for `__init__.spl` to replace repetitive `export use`
   - Desugars to `export use` statements
   - Paths are **relative to current module** — reference direct children, not current module's own name
   - Lint + auto-fix via existing EasyFix infrastructure (`L:structured_export_placement`, `L:flat_export_to_structured`)
   - Migration tool: `simple migrate --to-structured-export`
   - Design: `doc/design/structured_export_design.md`

3. **Simple Shell (`.ssh` DSL)** — Shell/DSL
   - `.ssh` files: Simple code with `std.shell.*` auto-imported
   - Command execution: `$(cmd)`, `@(cmd)`, `!? cmd`
   - Task system replacing Makefile: `task build depends_on: [test]:`
   - Fail-fast by default, typed errors via `Result<T, ShellError>`
   - Design: `doc/design/simple_shell_design.md`

4. **Extension-Config Registry** — Infrastructure
   - Unified registry mapping file extensions to compiler, prelude, default imports, mode
   - `.sdn` → SDN compiler, no prelude, data mode
   - `.ssh` → Simple compiler + `std.shell.*` default import, script mode, interpreter
   - `.spl` → Simple compiler + prelude, module mode (current behavior, now explicit)
   - Pattern overrides: `_spec.spl` → BDD imports, `_test.spl` → test imports
   - Project-level extension config in `simple.sdn`
   - Connects structured_export EasyFix rules to existing `src/app/fix/` pipeline
   - Design: `doc/design/extension_config_registry_design.md`

### Low (Future)
