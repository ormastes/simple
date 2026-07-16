# Pure-Simple tool and infrastructure hardening agent tasks

## Shared contract

Frozen manual steps and `qualification_*` helpers are defined in the detail
design. Sidecars must not invent parallel names or silent placeholders.

## Lanes

| Lane | Scope | Sidecar | Merge owner | Final reviewer |
|---|---|---|---|---|
| A | runner outcomes, sibling count, nested daemon, RSS design | `/root/test_runner_audit` | `/root` | primary highest-capability Codex |
| B | duplicate-check IO/security, lint/fmt/fix ownership | `/root/lint_dup_audit` | `/root` | primary highest-capability Codex |
| C | provenance, deployment, MCP/LSP/Linux/Windows wrappers | `/root/docs_scripts_audit` | `/root` | primary highest-capability Codex |
| D | requirements, architecture, system spec/manual, integration, verification | primary `/root` | `/root` | primary highest-capability Codex |

## Merge order

1. Primary model accepts sidecar design findings.
2. Implement disjoint roots with conflict checks before every edit.
3. Merge tests and generate the manual.
4. Primary model reviews all code, exclusions, NFR evidence, and done marks.

## Conflict policy

Windows `.cmd`, bootstrap/backend, and active test-runner files may be owned by
other sessions. Preserve unrelated changes and defer only the conflicting file,
recording its unmet requirement explicitly rather than folding foreign work into
this lane.

## Primary review decisions

- Accepted: safe duplicate IO facades, canonical lint parser, nonzero-child
  precedence, nested-daemon marker, native-first wrapper probes, and retained
  provenance/performance fields.
- Simplified: keep `TestFileResult` unchanged and classify at the aggregate CLI
  boundary instead of adding an outcome field to every constructor.
- Simplified: qualification helpers remain local to the canonical system spec;
  no one-consumer helper module is added.
- Preserved: the four primary manual steps defined by the primary model; sidecar
  substeps are implementation details, not competing public vocabulary.
