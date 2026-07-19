<!-- codex-design -->
# LLM Caret infrastructure access architecture

Date: 2026-07-18

## Decision

Implement selected feature option A as a thin compatibility capsule between
LLM Caret's existing trust boundary and existing ITF/canonical command routes.
The capsule does not own provider HTTP or authentication.

```text
model ToolCall
  -> tools.run_tool (known-tool + call-aware permission gate)
    -> infra_access.plan_infra_call (pure validation/conversion)
      -> capability result, or
      -> infra_access.execute_infra_plan (direct argv, bounded capture)
        -> gh | acli | aws | gws | bin/simple itf ...
```

## Public interface names

- Tool names: `infra_repo`, `infra_task`, `infra_storage`, `infra_mail`,
  `infra_wiki`.
- Types: `InfraPlan`, `InfraExecution`.
- Planning API: `plan_infra_call(family, input, workspace_root)`.
- Permission API: `infra_safety_class(family, input)` and
  `permission_decision_for_call(policy, call)`.
- Execution seams: `execute_infra_plan(plan)` and
  `execute_infra_plan_with(plan, runner)`.
- Checkers: `expect_supported_plan`, `expect_capability_error`,
  `expect_permission_denied` in the feature spec.

The input is structured JSON with `provider`, `operation`, optional `args`
(one direct argv item per newline), `format`, `endpoint`, and `raw_safety`.
Newline argv deliberately avoids a shell parser and preserves spaces inside one
argument. Credentials are never accepted as dedicated input fields.

## Compatibility routes

| Family | Provider | Production route | Compatibility surface |
|---|---|---|---|
| repo | GitHub | `gh` | `gh repo/pr/issue/workflow/run/api` |
| repo | Bitbucket | `bin/simple itf bb` | mapped `gh pr` subset plus provider raw |
| task | Jira | `acli jira` | work-item operations/JQL |
| task | GitHub | `gh issue` | declared issue subset |
| storage | S3/MinIO | `aws s3` or `aws s3api` | S3 URI and endpoint semantics |
| mail | Gmail | `gws gmail` | provisional transport behind Gmail resource operation names |
| mail | Outlook | `bin/simple itf outlook` | Microsoft Graph mapping subset |
| wiki | Confluence | `bin/simple itf wiki` | neutral page operation mapping |
| wiki | GitHub Wiki | `bin/simple itf github-wiki` | Markdown/git page mapping |

An absent executable is a route failure, not an emulated success. Capability
output names the adapter and transport and distinguishes supported, unsupported,
lossy, and provisional rows. The selected design does not claim every operation
of every canonical CLI.

## Permission ownership

`run_tool` remains the only executor entry. Infrastructure safety is derived
from the family plus operation before dispatch:

- read: capability, list, get, view, search, stat, status, run watch;
- write: create, update, comment, put, send, mark, approve, repository sync,
  workflow run;
- destructive: delete, remove, merge, close, cancel, overwrite;
- auth: login, logout, credential validation;
- raw: caller must supply one of the four classes.

Reads retain the current read policy. Writes/auth require a matching
`<tool>:<class>` grant or global explicit allowance. Destructive calls require
the distinct `<tool>:destructive` grant; a generic tool-name allow entry is not
enough.

## Data, streaming, and errors

`InfraPlan` retains family, provider, canonical operation, safety class,
adapter, transport, program, argv, format, support state, and explanation.
Execution output retains exit status, stdout/stderr, route identity, and result
class in stable JSON or human form. Provider output remains raw unless a shared
ITF adapter already normalizes it.

Object and attachment payloads travel by provider file/stdin conventions; the
compatibility capsule passes paths and `-` through argv and does not load payload
bodies. Workspace-bearing flags are validated under the policy root before
execution. The canonical bounded-process facade caps diagnostics/metadata at
30,000 bytes before unbounded allocation and terminates calls after 120 seconds.

## Startup and hot path

No provider probing, index, cache, or network action happens at Caret startup.
Capability/planning is static and linear in the short argv list. Every live call
creates one child process; there are no repeated tree scans or retry sleeps in
the request handler. Provider clients own authentication and retry policy.

Target: warm local plan/permission p95 below 200 ms, excluding child/provider
latency. Cache invalidation is not applicable because no provider state is
cached.

## Alternatives rejected

- Provider HTTP inside Caret: duplicates ITF/auth and weakens the trust boundary.
- Generic `bash`: loses typed capabilities and operation-aware permission.
- One lowest-common-denominator service: hides IDs, cursors, provider errors,
  and lossy differences.
- Shell command strings: create quoting/injection and secret-exposure risks.

## Requirement trace

REQ-LCSI-001/010/011 are owned by `tools.spl`; REQ-LCSI-002 through 009 and 012
by `infra_access.spl` and provider routes; REQ-LCSI-013 by the executable system
spec/manual; REQ-LCSI-014 by the guide. NFR-LCSI-001/003/005/006/007/009/011 are
enforced offline. Live and performance evidence for NFR-LCSI-002/008/012 are
separate opt-in gates and may not be inferred from contract tests.
