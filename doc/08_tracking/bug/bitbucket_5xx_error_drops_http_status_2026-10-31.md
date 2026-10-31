# Bitbucket 5xx errors drop the HTTP status from the message

Status: open, owner decision. Found 2026-10-31 by the emulated gh parity spec.

`bb_map_http_error` (`src/app/devhub/adapter_bitbucket_protocol.spl:310`) uses the raw
response body as the whole message for any status it does not name. A 500 with body
`server exploded` prints `error: server exploded`, with nothing saying it was a server
failure. GitHub through `gh` prints `HTTP 500`.

A fix prefixing `api_error (HTTP <status>): ` was tried and reverted: it made both parity
scenarios pass but broke `test/01_unit/app/devhub/redaction_followup_spec.spl`, scenario
"redacts provider bodies included in mapped errors", which pins the bare redacted body as
the exact message. Choosing between those two contracts is the owner's call.

## Reproduction

`test/03_system/app/devhub/feature/devhub_gh_parity_emulated_spec.spl`, scenarios "reports
an error for a 500 on bitbucket" and "names the status of a 503 on bitbucket". Both stay RED.

## Unblock

Either put the status in the message and update the pinned expectation, or have the
command layer print `ItfError.status_code`.
