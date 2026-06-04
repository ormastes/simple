# Research Common — Shared Format and Templates

## User Request Capture

Every research document MUST start with the user's original request:

```markdown
## User Request
> <original user request verbatim>
```

This preserves intent across the multi-LLM pipeline.

## Output Paths

| Artifact | Path |
|----------|------|
| Research | `doc/01_research/<domain>/<topic>/<feature>.md` |
| Feature requirements (draft) | `doc/02_requirements/<domain>/<topic>/<feature>_draft.md` |
| NFR requirements (draft) | `doc/02_requirements/nfr/<feature>_draft.md` |
| Requirement options | `doc/02_requirements/<domain>/<topic>/<feature>_options.md` |

### Domain directories (same across all doc phases)
`language/`, `compiler/`, `lib/`, `app/`, `os/`, `hardware/`, `platform/`, `runtime/`, `ui/`, `ml/`, `infra/`

## Research Document Format

```markdown
# <Feature> — Research & Implementation Plan

**Date:** YYYY-MM-DD  |  **Status:** Research Phase

## User Request
> <original request>

## 1. Problem Analysis (current state + requirements)
## 2. Proposed Solution (architecture + code examples)
## 3. Integration with Existing Infrastructure
## 4. Implementation Roadmap (phased tasks)
## 5. Testing Strategy
## 6. References
```

## Shared Rules

- Always check existing docs before duplicating research
- Search `doc/01_research/` for prior work on the same topic
- Use absolute dates (not "next Thursday")
- Reference file paths relative to repo root
- Research docs are inputs to the next pipeline step — keep them actionable
