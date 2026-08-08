<!-- codex-research -->
# SSpec Documentization Maintenance Research — TLDR

```sdn
sspec_doc_maintenance = flow(
  scan -> score_and_find -> preview -> confirm -> apply -> verify,
  outputs = [human, json, living_manual],
  safety = "never invent requirements or passing assertions"
)
```

- Living documentation layers stakeholder purpose/rules/workflows before
  execution evidence; it is not a prettified test log.
- Score named dimensions: clarity, behavioral structure, oracle strength,
  traceability, evidence, behavioral coverage, and maintainability.
- Keep blockers (placeholder pass, no execution, dangling REQ, invented oracle)
  outside the average so a high score cannot hide them.
- Emit SARIF-like findings: stable rule ID, severity/confidence, source span,
  rationale, remediation, fingerprint, and optional safe fix/suppression.
- Reuse deterministic EasyFix-style replacements. Default to preview; require
  explicit confirmation/apply; narrative and oracle edits remain suggestions.
- Spec-to-SSpec preserves requirement IDs/source locations and creates modern
  sections, steps, captures, and explicit fail-fast TODO assertions.
- Reuse canonical SPipe parser/docgen; retire simplistic parallel generators
  only through a compatibility plan.
- Core sources: Cucumber/Gherkin, Serenity living docs, Allure evidence, OASIS
  SARIF, OpenRewrite/clang-tidy/Semgrep safe codemods, Specmatic/Schemathesis.
