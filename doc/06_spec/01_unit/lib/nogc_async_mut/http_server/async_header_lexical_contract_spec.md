# Async HTTP header wire grammar

Requirement: REQ-LIB-NOGC-ASYNC-MUT-001.

Executable specification: `test/01_unit/lib/nogc_async_mut/http_server/async_header_lexical_contract_spec.spl`.

These scenarios exercise the production `HttpRequestParser`, without a stub parser.

| Scenario | Expected behavior |
| --- | --- |
| Whitespace before the colon | Reject SP/HTAB before the colon and store no header. |
| Separators and non-ASCII names | Reject HTTP separator punctuation and Unicode names. |
| Valid token punctuation | Preserve every allowed tchar punctuation character. |
| Control bytes in names | Reject all ASCII C0 controls and DEL. |
| Control bytes in values | Reject every C0 control except HTAB, including at either edge before trimming; reject DEL. |
| Legal field values | Preserve interior HTAB and Unicode text; trim surrounding whitespace. |
| Fragmented malformed header | Report the lexical diagnostic, enter Error and remain incomplete after further input. |
| Malformed framing | Retain the missing-colon and empty-name error. |

Status: AUTHORED_UNEXECUTED (2026-10-16). No qualified self-hosted full CLI was available in this validation lane. Source review and whitespace checks do not establish runtime correctness.

The broader tracked bug also covers Host presence, authority validation and absolute-form target agreement. These scenarios do not claim those requirements are repaired.
