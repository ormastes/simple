# Code-action query/LSP wire contract

Source: `test/01_unit/app/lsp/code_action_wire_contract_spec.spl`.
Requirement: REQ-LSP-CODEACTION-EDIT-001.
Bug: `lsp_code_action_edit_emit_parse_mismatch_2026-06-16`.

## Evidence status

**UNRUN / TEST_BLOCKED.** Fifteen scenarios are authored; zero behavioral
examples have been executed for this candidate. No qualified self-hosted full
CLI is deployed. The tracked Rust bootstrap seed is not used for ordinary
verification. This manual is a test plan, not generated passing evidence.

The existing six `code_action_edit_roundtrip_spec.spl` scenarios are retained
unchanged and remain required alongside this contract.

## Scenarios

| Group | Contract exercised |
|---|---|
| Exact | Parse `params.range.start` and URI with ordinary JSON whitespace; send one-based query line and separate `--format`, `json` argv values. |
| Exact | Serialize the actual `Foo.new()` quickfix, convert the query array to LSP, apply the returned deletion, and assert `Foo()`. |
| Exact | Retain both constructor replacements and apply both to obtain the intended source. |
| Adjacent | Preserve multiple actions, preferred flags, command and data. |
| Adjacent | Handle reordered/pretty JSON, escaped titles and replacement strings containing JSON-looking field names. |
| Adjacent | Reject an entire edit when a later replacement has missing, null or non-string text; preserve valid empty deletion strings. |
| Adjacent | Reject negative, inverted, fractional or absent range positions. |
| Adjacent | Convert byte offsets to zero-based UTF-16 positions for supplementary characters, multiline edits and CRLF. |
| Adjacent | Reject mid-scalar, mid-CRLF, inverted and out-of-bounds offsets. |
| Adjacent | Apply bare-pass replacement while retaining tabs, trailing spaces and comments; reject already-named pass functions. |
| Adjacent | Preserve authoritative document URIs/versions and separate URI targets. |
| Adjacent | Disable positional constructor suggestions whose field mapping is unavailable. |
| Adjacent | Reject malformed arrays, ignore child diagnostic headings, and reject requests missing a valid code-action range. |

## Owner and performance design

The live handler uses a pure typed-JSON leaf for request and result conversion.
The query producer uses that same leaf's structural serializers. No additional
process, environment, filesystem or index lookup is introduced. Metadata and
all replacements remain attached to their action; invalid edit arrays are
rejected atomically. Existing standalone JSON/tab rows remain compatible.
Single source-path changes are rebound to the request URI; already-standard
URI targets retain authority. Multiple ambiguous non-URI path targets are
rejected rather than redirected to the wrong document.

One source map is built per query source read and discarded with that request.
It stores line starts, uses binary search per endpoint and scans only the
endpoint's line prefix for UTF-16 width. No per-replacement file reread or
whole-source scan is added. The typed JSON implementation is already a
dependency of the LSP query-command owner. Startup, representative warm request
latency and maximum RSS measurements remain **UNRUN**; compare the previous
head and this candidate on the same qualified producer and realistic fixture
before admission. Do not claim a performance result from source inspection.

## Required execution before admission

Run both code-action specs using a qualified self-hosted CLI. Also run the
required compiler, library, MCP and LSP checks, MCP interpreter integration,
core runtime smoke and MCP native smoke. Capture actual positive counts and
producer/source identity. Package publication is unchanged.
