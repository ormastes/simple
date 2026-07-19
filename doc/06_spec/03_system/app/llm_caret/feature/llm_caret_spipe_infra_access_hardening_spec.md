# LLM Caret + SPipe Infrastructure Access Hardening

Status: executable spec authored; current-tree generation and execution await a
deployable full-CLI self-hosted runtime, as recorded below.

Source:
`test/03_system/app/llm_caret/feature/llm_caret_spipe_infra_access_hardening_spec.spl`

Requirements:
`doc/02_requirements/feature/llm_caret_spipe_infra_access_hardening.md`

NFRs:
`doc/02_requirements/nfr/llm_caret_spipe_infra_access_hardening.md`

## Purpose

This behavioral manual covers the five typed Caret infrastructure families,
their canonical route plans, the call-aware permission boundary, normalized
provider evidence, and the reviewed documentation provenance. It is not live
provider evidence and does not claim full Claude CLI parity.

## Stable execution steps

1. Discover infrastructure tool capabilities without provider access.
2. Plan canonical provider argv without shell interpolation.
3. Deny ungranted mutation before provider execution.
4. Require a distinct destructive-operation grant.
5. Execute the planned production route through the injected runner seam.
6. Preserve route identity and provider output in stable JSON.
7. Reject unsupported lossy or workspace-escaping requests explicitly.

## Scenarios

### REQ-LCSI-001 and REQ-LCSI-010: typed registration

Given the default non-interactive policy, capability calls for `infra_repo`,
`infra_task`, `infra_storage`, `infra_mail`, and `infra_wiki` traverse
`run_tool` and return offline capability JSON without launching a provider.

### REQ-LCSI-002 and REQ-LCSI-011: direct argv

`repo/github/pr.view` plans executable `gh` with argv
`[pr, view, 42, --repo, org/project]`. No shell executable or `-c` argument is
present, and a value containing spaces remains one argv item.

### REQ-LCSI-003: repositories

GitHub repository/PR/issue/workflow/run operations use `gh`. The supported
Bitbucket PR subset uses `bin/simple itf bb`. Bitbucket workflow requests return
an explicit capability error.

### REQ-LCSI-004: tasks

Jira work items use `acli jira workitem`; JQL remains one argument. GitHub tasks
use the declared `gh issue` subset. Provider-native workflows and fields are not
invented.

### REQ-LCSI-005: storage

S3 and MinIO use `aws s3`/`aws s3api`; MinIO adds `--endpoint-url`. `s3://`
identities remain intact, and object payloads use provider file/stdin operands
rather than a JSON body buffered by Caret.

### REQ-LCSI-006: mail

Gmail resource operations map to the explicitly provisional `gws gmail`
transport. The implemented Outlook subset maps to `bin/simple itf outlook`.
Unsupported Outlook labels, drafts, or send operations fail as capabilities.

### REQ-LCSI-007: wikis

Neutral page operations map to `bin/simple itf wiki` for Confluence and
`bin/simple itf github-wiki` for git-backed GitHub Wiki Markdown. Confluence
update accepts `--from-file` for non-interactive use.

### REQ-LCSI-008: capability truth

Capabilities name provider, route, supported operations, lossy semantics, and
provisional transports. Unknown providers and unsupported mappings fail before
process execution.

### REQ-LCSI-009: normalized evidence

The injected runner returns opaque provider ID, cursor, and request ID fields.
Stable JSON retains those bytes together with family, provider, operation,
safety, adapter, transport, status, and exit code.

### REQ-LCSI-010: permission classes

An ungranted issue creation is denied before process execution. A generic
`infra_wiki` grant does not authorize page deletion; only
`infra_wiki:destructive` or the explicit global dangerous policy does.

### REQ-LCSI-011: validation

Tool JSON containing token/password/secret fields is rejected. Absolute paths
outside the workspace and `..` traversal are rejected before route execution.
Raw provider argv requires an explicit `raw_safety` class.

### REQ-LCSI-012: production seam identity

`execute_infra_plan_with` and `execute_infra_plan` consume the same `InfraPlan`.
The offline runner therefore verifies the exact program, argv, adapter, and
transport later used by production; it is not presented as a live provider hit.

### REQ-LCSI-013 and REQ-LCSI-014: evidence and provenance

The spec checks the selected requirements and the guide's `gpt-5.4-mini` draft
plus primary high-capability review provenance. It explicitly rejects using
this feature as full Claude CLI parity evidence.

### NFR-LCSI-008: local planning latency

The executable spec records 50 warm planning samples, sorts them, selects the
nearest p95 sample, and requires less than 200,000 microseconds. Child-process
and provider latency are excluded.

## Opt-in live matrix

`test/03_system/e2e/llm_caret_infra_access_live_spec.spl` supplies read-only
rows for GitHub, Bitbucket, Jira, S3, MinIO, Gmail, Outlook, Confluence, and
GitHub Wiki. Every row asserts provider, adapter, transport, read safety, and
successful exit, then records elapsed microseconds and that no destructive grant
was required. No row runs unless its `LCSI_LIVE_<PROVIDER>=1` flag is set.

## Current execution blocker

Current `origin/main` contains the bounded-process facade/runtime registrations
and the nested string-`split` lowering fix. In this revived worktree, the
canonical bootstrap passed Stage 3 but the full-CLI Stage 4 was terminated by
SIGTERM (exit 143), so neither runtime acceptance command could be rerun without
substituting a bootstrap-only seed. This remains the permitted manual companion,
not falsely labeled generated output. See the two linked bug records for the
source and bootstrap evidence.
