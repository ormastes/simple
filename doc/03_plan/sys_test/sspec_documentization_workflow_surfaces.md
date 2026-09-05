# SSpec Documentization Workflow Surface Manifest

Schema: `ssdoc-workflow-surfaces/v1`
Contract revision: `REQ-SSDOC-011/2026-08-03`

This sorted manifest defines the generic workflow surfaces that must stay
synchronized. It is structural documentation evidence only. Presence of words
in these files does not prove scanner, scaffold, apply, documentize, or import
behavior; executable owner and CLI tests remain authoritative.

## Required contract clauses

Each applicable surface must communicate, at its phase-appropriate depth:

1. Run `simple sspec-maintain scan <spec>` for changed SSpec/manual pairs and
   review all seven scores plus stable findings.
2. Block completion for blockers, missing/stale mirrors, configured policy
   failure, machine-output contamination, or unresolved scaffolds presented as
   coverage.
3. Keep `improve` preview-only until exact confirmation; applied edits retain
   rollback material and never rewrite assertions, REQ bindings, evidence, or
   authored prose mechanically.
4. Preserve scaffold source path/hash/line and explicit REQ identity; unresolved
   oracles fail fast and generated prose never becomes a passing assertion.
5. Keep SPipe as the complete-manual owner; `documentize` composes observed
   provenance/scoring around authored SPipe output.
6. Treat `spec-to-spipe` as the planned canonical external-standard command and
   `spec-to-sspec` as its future compatibility route to the same implementation.
   Phase 0 contracts are not production CLI availability evidence.

## Sorted surface inventory

| Path | Phase | Required emphasis |
|---|---|---|
| `.agents/skills/design/SKILL.md` | design | scores, failure policy, scaffold/manual/import ownership |
| `.agents/skills/impl/SKILL.md` | implementation | confirmed apply, rollback, fail-fast scaffold, SPipe composition |
| `.agents/skills/verify/SKILL.md` | verification | release-blocking failures, prose/provenance review, compatibility boundary |
| `.gemini/commands/design.toml` | design | traceability, scaffold provenance, SPipe/import ownership |
| `.gemini/commands/impl.toml` | implementation | scan, apply safety, no invented prose/oracle |
| `.gemini/commands/refactor.toml` | refactor | lint/duplicate/scan peer gate, rollback, ownership preservation |
| `.gemini/commands/sp_dev.toml` | development entrypoint | complete concise contract and command availability boundary |
| `.gemini/commands/verify.toml` | verification | fail-closed policy, authored manual/scaffold review, compatibility boundary |

## Structural audit rule

Audit the exact sorted path set above and review its phase-specific meaning.
Token/source checks may report a missing or stale surface, but must be labeled
`structural synchronization` and must never count as behavioral or conformance
evidence. Any added generic design, implementation, refactor, test, or verify
surface must update this manifest and the REQ-SSDOC-011 lane inventory in the
same change.
