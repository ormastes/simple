<!-- codex-research -->
# LLM Caret + SPipe infrastructure access hardening: local research

Date: 2026-07-18

## Goal

Harden LLM Caret as a tested Simple-native development environment, integrated
with SPipe and standardized infrastructure adapters for task tracking, object
storage, email, wikis, and repository hosting. Reuse existing provider code and
present familiar compatibility surfaces without hiding provider differences.

## Method and concurrent-work boundary

Three read-only sidecars audited implementation, existing documents, and
current official provider interfaces. The primary model reviewed and merged the
results. No broad tests were run because unrelated compiler/test sessions are
active. No current dirty file overlaps `src/app/llm_caret`, `src/app/itf`, or
their focused tests. Related dirty SPipe skill files belong to other sessions
and must not be folded into this lane.

## Current LLM Caret implementation

- `src/app/llm_caret/claude_cli.spl` is a compact wrapper around the installed
  `claude` executable.
- `src/app/llm_caret/tools.spl` has one permission gate, but recognizes only
  `bash`, `read_file`, `write_file`, `list_dir`, and `glob`.
- LLM Caret imports no `app.itf` module and exposes no typed infrastructure
  service tools.
- There is no `src/app/llm_caret/main.spl` and no Caret command in the
  canonical CLI dispatch table.
- Focused unit coverage exists for tool permission/path behavior, retry, and
  redaction under `test/01_unit/app/llm_caret/`.

### Claude-full parity caveat

`src/app/llm_caret/claude_full/` contains hundreds of deterministic parity
models and specs, but is not a runnable full Claude CLI. Its `main.spl` exposes
route helpers rather than `main()`, task files are often name/route models, and
`entrypoints/agentSdkTypes.spl` explicitly returns multiple "not implemented"
results. Current parity system specs mainly validate matrices and source-shape
coverage, not end-to-end behavior.

This conflicts with requirements that prohibit any unimplemented parity row.
The newer behavior-based reset design and older LOC/row parity gates must be
reconciled before any full-parity completion claim.

## Current infrastructure tool implementation

`src/app/itf/main.spl` is the existing provider CLI. It dispatches wiki, Jira,
raw API, auth, Bitbucket, MinIO, Outlook, and daily-debug commands.

| Area | Existing path | Current truth |
|---|---|---|
| GitHub | `src/app/itf/adapter_github.spl` | Thin `gh` passthrough explicitly marked as a stub; not dispatched or tested. |
| Jira | `adapter_jira.spl`, `adapter_jira_curl.spl` | `acli jira workitem` builder plus tested REST/curl fallback; command coverage is incomplete. |
| Bitbucket | `adapter_bitbucket.spl`, `adapter_bitbucket_curl.spl` | PR/comment/approval/merge/status models exist; wired pure adapter builds requests but does not transport them, while tested curl fallback is not wired. |
| MinIO/S3 | `adapter_minio.spl`, `adapter_minio_mc.spl` | S3/SigV4 surface and `mc` fallback exist; pure adapter is wired, but live evidence uses `mc` and an open runtime transport/binary-body gap remains. |
| Microsoft mail | `adapter_outlook.spl`, `adapter_outlook_curl.spl` | Graph models and curl fallback exist; wired pure adapter does not execute its request tuple, while tested fallback is not wired. |
| Gmail | none | Missing. |
| Confluence | `adapter_confluence.spl`, `cmd_wiki.spl` | Wiki command surface exists; request builders do not currently execute authenticated transport. |
| GitHub Wiki | none | Missing; should use git-backed Markdown semantics. |

Seventeen ITF unit specs cover many parsers/builders. Six opt-in E2E specs
cover curl Jira/Bitbucket and `mc` MinIO. There is no focused coverage for the
GitHub passthrough, Confluence transport, Jira ACLI execution, Gmail, ITF
dispatch, or the provider path actually wired by Outlook/Bitbucket commands.

## Current SPipe relationship

`src/lib/nogc_async_mut/spipe_process_harness/core.spl` and
`src/app/spipe_process_harness/main.spl` normalize LLM hook events and manage
state, gates, HUD, and deployment. They do not provide infrastructure service
access. The existing ITF daily-debug pipeline composes mail, Jira, and MinIO,
but it is separate from LLM Caret's permission/tool registry and from the SPipe
process harness.

There is no unified behavioral SPipe spec/manual that proves Caret permission
gating, provider capability selection, canonical argument conversion, and
offline error handling across all infrastructure categories.

## Existing documents and evidence quality

- `doc/05_design/app/spipe/spipe_infra_arch.md` designed provider-specific ITF
  commands, not canonical CLI compatibility. It also says production adapters
  use pure Simple HTTP while the later remaining-work plan records curl/`mc`
  shims because transport is blocked.
- `doc/03_plan/app/spipe/spipe_infra_remaining_2026-04-26.md` remains deferred:
  Microsoft Graph live verification, authenticated Jira/Bitbucket writes,
  daily-debug, and review-pipeline dogfood are incomplete.
- Existing provider research covers MinIO/S3, Graph mail, and Bitbucket REST,
  but not the comparative canonical interfaces, Gmail, GitHub/`gh`, Jira ACLI,
  or GitHub Wiki conversion.
- `doc/07_guide/app/llm_caret_usage.md` documents the compact Caret tool gate,
  TUI, retry, and redaction, but not infrastructure access.
- The already-selected `pure_simple_tool_infra_hardening` requirements concern
  compiler/toolchain provenance and must not be repurposed for this feature.

## Root design findings

1. Reuse ITF provider code; do not add provider HTTP logic inside LLM Caret.
2. Do not expose generic unrestricted `bash` as the infrastructure API.
3. Add typed service tools behind the existing Caret permission gate, with
   explicit read/write/destructive classes and capability discovery.
4. Put canonical argument/output conversion in a shared compatibility layer,
   then route to ITF/provider adapters or a validated installed CLI.
5. Keep provider IDs, pagination cursors, error codes, and raw escape hatches.
6. Test offline contracts first; live provider tests are separate opt-in
   evidence and cannot be simulated by parser-only specs.
7. Replace contradictory LOC/source-shape completion claims with behavioral
   evidence only after the user selects that broader requirement change.

## Missing artifacts

- Selected feature and NFR requirements for standardized infrastructure access.
- Architecture and detail design for the compatibility/tool boundary.
- A feature-level SPipe system spec, generated manual, test plan, and agent task
  plan with sidecar lanes, merge owner, and final reviewer.
- A detailed operator/developer guide drafted by an explicitly lower-capability
  sidecar and reviewed/corrected by the primary high-capability model.
- Focused unit/integration/live tests for the actual wired provider paths.

## Recommended sequencing

Select requirements first. Then design the smallest typed compatibility layer,
write the behavioral SPipe spec before implementation, wire one provider per
category using existing code, add missing Gmail/GitHub Wiki adapters only if
selected, and verify offline plus explicitly configured live gates.
