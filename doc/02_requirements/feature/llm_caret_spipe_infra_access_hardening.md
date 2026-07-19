<!-- codex-research -->
# LLM Caret + SPipe infrastructure access hardening requirements

Selected: feature option A (thin typed delegation) on 2026-07-18.

- REQ-LCSI-001: LLM Caret must expose typed infrastructure tools for repository
  hosting, task management, object storage, mail, and wiki operations, and every
  call must traverse the existing `run_tool` permission gate.
- REQ-LCSI-002: LLM Caret must delegate provider behavior to existing ITF
  handlers/adapters or validated canonical CLIs; it must not duplicate provider
  HTTP/authentication implementations inside the Caret capsule.
- REQ-LCSI-003: Repository operations must present a `gh`-compatible command
  vocabulary for GitHub and mapped Bitbucket operations, including repository,
  pull-request, issue, workflow/run capability discovery, stable machine output,
  and an explicit raw/provider escape hatch.
- REQ-LCSI-004: Task operations must present an `acli jira`-compatible work-item
  vocabulary for Jira and a documented GitHub Issues subset; workflows, boards,
  JQL, milestones/fix versions, and custom fields must map only through declared
  capabilities or explicit configuration.
- REQ-LCSI-005: Object-storage operations must present `aws s3`/`aws s3api`
  semantics for S3 and MinIO, preserve `s3://` URIs and endpoint selection, and
  support streaming-safe list/get/put/stat/delete/presign capability routing.
- REQ-LCSI-006: Mail operations must present Gmail REST resource semantics for
  messages, threads, labels/folders, drafts, attachments, search, and send;
  Gmail and Microsoft Graph mappings must preserve MIME, provider IDs, and
  unsupported or lossy distinctions.
- REQ-LCSI-007: Wiki operations must present a neutral
  `page list|get|create|update|delete|search` vocabulary; Confluence must retain
  page/space/parent/version/body-representation data, while GitHub Wiki must map
  pages to Markdown files and git-backed revisions.
- REQ-LCSI-008: Every tool family must expose provider and operation capability
  discovery. Unsupported operations and lossy conversions must fail explicitly
  instead of silently degrading or fabricating parity.
- REQ-LCSI-009: Normalized results must retain provider name, provider resource
  IDs, opaque pagination cursors, provider error code, HTTP/CLI status, request
  ID when available, retry metadata, and raw provider output when requested.
- REQ-LCSI-010: Infrastructure operations must be classified as read, write,
  destructive, or authentication operations. Reads follow the configured
  read policy, writes remain denied by default unless granted, and destructive
  operations require a distinct explicit grant.
- REQ-LCSI-011: Canonical arguments must be converted to direct argv arrays or
  in-process calls with no shell interpolation. Credentials and secret content
  must enter through stdin, credential stores, or environment indirection.
- REQ-LCSI-012: The production route for each claimed provider must execute the
  same adapter/transport proven by its focused tests. Request-builder, parser,
  fallback, and live-transport evidence must be reported as different states.
- REQ-LCSI-013: SPipe must provide an executable behavioral system spec and a
  mirrored generated/manual guide covering tool registration, conversion,
  capability errors, permission denial/grants, provider selection, stable
  output, and representative offline provider responses.
- REQ-LCSI-014: The implementation must update the operator/developer guide,
  preserve the recorded smaller-model draft plus high-capability review
  provenance, and must not use this feature as evidence that all Claude-full
  parity rows or the full Claude CLI are complete.
