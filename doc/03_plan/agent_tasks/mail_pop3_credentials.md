# Mail lane ownership

- Parent: protocol/credential implementation, docs, review integration, PR owner.
- `mail_tests`: offline regressions, modern SSpec and mirrored manuals.
- `mail_review`: independent source/security review, read-only findings.
- Lower-model sidecars: N/A. All agents use the inherited model.
- Final reviewer: parent after independent findings are addressed.
- SPipe deployment is a separate agent-owned branch and must not be included
  in the mail commit. Shared-workspace changes remain untouched.
