# Source-open protocol adapter — authored manual

Execution status: UNVERIFIED. This is an authored mirror pending admitted SPipe generation and maintenance scoring; it is not a process-protocol receipt.

The scenarios call the real in-process dispatcher and expect default outline to return native L1 folded source, reject malformed/duplicate-key requests and invalid paths, open an actual empty fixture, and reject stale or unbound continuation. Serialization scenarios round-trip Korean/emoji/decorations/control characters, escape bidi controls, preserve declared limitations and enforce byte rather than character budgets.

Source: `test/01_unit/app/mcp/source_open_contract_spec.spl`. Fixtures: `test/fixture/source_view/empty.txt` and `unicode.txt` (CRLF intentionally retained). Pending: execution against the admitted runtime, real MCP framing/discovery smoke, generated manual review and seven-score maintenance assessment.

## Serialized JSON-RPC ID boundary

Four additional scenarios call the registered dispatcher and public response helper. They assert actual parsed envelopes, exact 128/129 serialized byte admission, an 18002-byte multibyte ID without echo, malformed/non-scalar rejection, and preserved null/string/integer/fractional IDs. Successful responses, payload-overflow fallbacks, malformed-body errors and oversized-body errors remain within the 16 KiB whole-wire ceiling. Invalid IDs produce the canonical -32600 error with null ID before request processing.

New helpers use the `mcp_source_` prefix. Byte oracles and the admission boundary use canonical `std.common.string_core.str_len`, independent of the text-length migration. Source reproduction: the prior owner echoed unchecked IDs from both its success-overflow fallback and early error paths. Authored prevention scenarios are **NOT_RUN**; no process lifecycle, runtime, docgen, coverage or performance PASS is inferred. Raw behavior and authentication limitations remain unchanged; default Simple outline is now native L1.

Registered-route structural scenarios assert folded class headers, focused exact method text, parent headers on later depth-two pages, query/result-bound continuation and whole-wire caps. These authored scenarios are NOT_RUN, not runtime qualification.

E1 compatibility control decodes oversized-response fallback content as JSON and asserts status/error, completeness/not_evaluated and the exact reason, while preserving supported scalar IDs and the whole-wire ceiling.
