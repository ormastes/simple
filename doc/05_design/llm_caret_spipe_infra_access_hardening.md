<!-- codex-design -->
# LLM Caret infrastructure access detail design

## Scope

This design implements the selected A + 2 boundary. It adds no Caret dashboard
or other UI, so TUI/GUI design is N/A. Existing tool-call rendering continues
to display the tool name and the fenced/redacted result.

## Input contract

Every infrastructure tool accepts:

| Field | Required | Meaning |
|---|---:|---|
| `provider` | yes except capability-all | provider identity |
| `operation` | yes | canonical dotted operation or `capabilities`/`raw` |
| `args` | no | newline-delimited direct argv items |
| `format` | no | `human` (default), `json`, or `ndjson` |
| `endpoint` | MinIO only | non-secret endpoint passed as `--endpoint-url` |
| `raw_safety` | raw only | explicit read/write/destructive/auth class |

Empty argv lines are omitted. NUL-like control input, credential-bearing argv,
mail body/MIME argv,
unsupported format,
unknown provider/operation, missing MinIO endpoint, unsafe workspace paths, and
ambiguous raw safety fail before process launch.

## Planning algorithm

1. Parse only known scalar JSON fields.
2. Validate family, provider, operation, output format, and argv count/length.
3. Classify safety from an exact operation table; `raw` uses validated
   `raw_safety`.
4. Map canonical operation to a fixed executable and fixed prefix.
5. Append user argv items without shell parsing/interpolation.
6. Add machine-output flags only where the route supports them.
7. Validate path-bearing `--file`, `--out`, `--output`, `--from-file`,
   `--repo-path`, and local operands under `workspace_root`.
8. Return supported plan or explicit capability/validation error.

## Operation mappings

- Repository/GitHub maps dotted paths to matching `gh` groups. Bitbucket maps
  `pr.view`, `pr.create`, `pr.comment.list`, `pr.comment.create`, `pr.approve`,
  `pr.merge`, and `pr.status` to ITF; other GitHub-only groups fail explicitly.
- Task/Jira maps `workitem.*` to `acli jira workitem`; `search` becomes
  `workitem search`. GitHub maps the issue subset to `gh issue`.
- Storage maps `s3.*` and `s3api.*` to AWS CLI. MinIO inserts its endpoint
  before the same groups. Payload operations require provider streaming/file
  arguments rather than JSON body content.
- Mail exposes Gmail resource names through `gws gmail` and maps Outlook
  folders/messages/get/move/mark to ITF. Unsupported send/draft/label mappings
  are capability errors until their production route exists.
- Wiki maps Confluence operations to ITF. GitHub Wiki list/get/search reads use
  direct `git` argv; create/update/delete/raw retain the ITF helper.

## Result contract

JSON/NDJSON output contains `family`, `provider`, `operation`, `safety`,
`adapter`, `transport`, `status`, `exit_code`, `stdout`, and `stderr`. Capability
output adds the supported operation list and `lossy`/`provisional` notes.
Human output begins with the same route identity, then provider stdout/stderr.
No result fabricates HTTP/request/cursor values that the child route omitted.

## Error handling

- validation/capability error: no child process, `is_error=true`;
- permission error: no planner execution, `is_error=true`;
- missing CLI/auth/provider failure: child exit retained, `is_error=true`;
- output cap: captured diagnostics report truncation, never a false success;
- destructive raw call without distinct grant: denied before execution.

## Testing seams

`execute_infra_plan_with` receives a runner function and is the only test seam.
Offline specs assert exact program/argv and normalized output using a fake
runner; production calls use the same `InfraPlan` through bounded process
execution. Object/attachment payloads use file/stdin routes rather than captured
output. Live smoke specs are opt-in and must print adapter, transport, provider,
safety, elapsed time, and grant state.


## Manual SPipe vocabulary

The executable spec uses these stable steps:

1. `Discover infrastructure tool capabilities without provider access`
2. `Plan canonical provider argv without shell interpolation`
3. `Deny ungranted mutation before provider execution`
4. `Require a distinct destructive-operation grant`
5. `Execute the planned production route through the injected runner seam`
6. `Preserve route identity and provider output in stable JSON`
7. `Reject unsupported lossy or workspace-escaping requests explicitly`
