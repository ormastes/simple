<!-- codex-research -->
# SSpec Documentization Maintenance Requirements — TLDR

```sdn
sspec_maintain = command(
  operations = [scan, improve, scaffold, documentize],
  owners = [spipe_docgen, easy_fix, existing_spipe_lint],
  writes = "preview then explicit confirm/apply"
)
```

- Dedicated `simple sspec-maintain` command; no fourth doc generator.
- Explainable seven-dimension score plus blocker findings and policy exits.
- Human, pure JSON, and SARIF-compatible report with stable `SSDOC-*` IDs.
- Inspect both SSpec source and its canonical mirrored manual.
- Reuse EasyFix; preview by default; atomic explicit apply; retain rollback.
- Scaffold Markdown requirements into modern SSpec while preserving source IDs;
  unresolved behavior is an explicit failing stub, never a pass.
- Professional manuals layer stakeholder flow before execution evidence and may
  include a score/findings appendix without inventing prose.
- Keep `spipe-docgen` compatible and label `spec-gen`/older tools accurately as
  legacy pending a separate migration.
- Update refactor, test, SPipe, verification, command, template, wiki, and guide
  surfaces together.
