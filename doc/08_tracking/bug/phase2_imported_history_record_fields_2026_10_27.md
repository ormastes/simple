# Phase 2 imported indexed history-field workaround

Status: WORKAROUND VERIFIED for the shared record view; compiler defect OPEN.
No Phase2 compiler was rebuilt or replaced.

The existing pure-Simple Phase2 producer
`1ad6ea53c67f3e01efc5c1b0ac8aa4dcef184a0987b4d3c806c59e14e96be584`
misreads non-first fields after indexing an imported McpT32HistoryItem array.
The original state fixture fails the last request-ID check. Three bounded,
changed-input diagnostic builds localized and contrasted the operation:

- Core counts, history length and first command pass; assertion5 fails.
- Explicitly typed indexed local returns command `cmd-499` for result and
  request_id too. Decimal formatting correctly returns499.
- A directly constructed imported record reads distinct fields correctly.
  A view function in the record's declaring owner reads the indexed record as
  `(cmd-499,value-499,session,core,request-499)` correctly.

`t32_history_fields` transfers those five fields as a typed tuple. The actual
production-owner native fixture compiled/linked and ran all11 original semantic
checks, exit0: core counts,500-entry threshold,251-entry suffix, order, result,
session/core identity and final request ID. Evidence:
`build/tooling-phase2/workaround-state/owner-view-run/`, owner-view.spl,
owner-view-runtime.log. Earlier failed binaries/logs remain in the same parent.
This is focused native evidence, not a canonical SSpec or complete server PASS.

The real shared history serializer uses the owner view and retains appended
JSON entries. Legacy main declares a different four-field history record; its
two serializers use a separate locally typed four-field view. Representations
and wire keys/order/escaping/count limits are preserved, not unified by unsafe
casts. The legacy integration is source-reviewed, not independently executed.
New/updated SSpec expectations preserve the exact field values and remain UNRUN
while the general native test runner is blocked.

Remove the workaround only after the original indexed-field form preserves
every distinct field under a qualified compiler and the actual history callers
pass. Do not change expected values to the corrupted first field or reinterpret
the record layout. No compiler rebuild is authorized by this record.

## Other fixes considered

Astra reviewed landed PRs5014,4997,5006. Typed Result call boundaries, field-name
forwarding precedence and fresh-array ownership changes are reasonable in their
respective scopes, but do not establish this old producer's field-read behavior.
They remain upstream; no duplicate cherry-picks or global compiler flags were
used. Compiler-source changes do not alter this immutable Phase2 executable.
