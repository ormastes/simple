# Accessor Field-Access Tooling — Completion Plan (TL;DR)

Date: 2026-06-07 · Full: [accessor_fix_tooling_completion_plan.md](accessor_fix_tooling_completion_plan.md)

Field-access rewrite shipped (199→111 ACC001 cleared; `L:short_grammar_field_access`
emitted by `bin/simple fix`/`lint`). Two gaps remain.

**A. LSP code-actions** — the LSP shells only `check`, so lint/EasyFixes aren't
shown. Add: in-process `Linter.lint_source` diagnostics + a
`textDocument/codeAction` handler mapping `EasyFix.Replacement` (byte offsets) →
LSP `WorkspaceEdit` (line + **UTF-16** columns). Advertise `codeActionProvider`.
Live only after a bootstrap rebuild.

**B. Clear the 111** — they are type-ambiguous (a real same-named method exists),
so deletion needs **receiver types**. Steps: (0) classify — keep intentional
mocks/forwarding/examples; (1) resolve receiver type per call **via the compiler's
type pass, in-process** (preferred over LSP round-trips); (2) rewrite only
C-typed calls then delete C's wrapper, **fail closed** on any unresolved /
`&:N` / `_.N` / `ANY` usage; (3) gate with dry-run + 0-dangling + worktree
baseline-vs-sweep + bootstrap; (4) pilot 2–3 names then expand.

Independent; do **B first** (reduces the metric), **A second**.

```sdn
plan {
  shipped: "field-access rewrite + ACC001 199->111"
  A: "LSP: lint diagnostics + EasyFix quickfix code-actions"
  B: "type-aware delete of 111 ambiguous wrappers (compiler-driven, fail-closed)"
  shipped -> B -> A
  gate: "dry-run + 0-dangling + baseline-vs-sweep + bootstrap, in isolated worktree"
  B -> gate
}
```
